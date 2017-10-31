{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Data.Text.Lazy as TL
import Data.Monoid ((<>))
import qualified Web.Scotty as W
import Data.Pool (createPool, destroyAllResources)
import qualified Database.PostgreSQL.Simple as PG
import qualified Network.Wai.Middleware.Static as M
import Network.Wai.Middleware.RequestLogger (logStdoutDev)
import Text.Blaze.Html.Renderer.Text (renderHtml)

import App (PGPool, Action, runQuery)
import Config.Config (respondentKeyFieldName, baseURL)
import Config.Server.Config (pgCreds, port)
import qualified Modes
import FormEngine.FormData
import qualified FormStructure.FormStructure as Structure
import qualified Model.Respondent as R
import Model.Result
import PageGenerator (renderPage)

main :: IO ()
main = do
  pool <- createPool (PG.connect pgCreds) PG.close 1 300 5
  W.scotty port (routes pool)
  destroyAllResources pool

routes :: PGPool -> W.ScottyM ()
routes pool = do
  W.middleware M.static
  W.middleware logStdoutDev
  W.get "/" (rootHandler pool)
  W.get "/wrong" wrongRespondentHandler
  W.post "/save" (saveHandler pool)
  W.post "/submit" (saveHandler pool)
  W.get "/submitted" submittedHandler
  W.post "/api/getData" (getDataHandler pool)

rootHandler ::  PGPool -> Action
rootHandler pool = do
    ps <- W.params
    let maybeRespondentKey = lookup (TL.fromStrict respondentKeyFieldName) ps
    case maybeRespondentKey of
      Nothing -> W.html $ renderHtml $ renderPage Modes.ReadOnly
      Just respondentKey -> do
        maybeRespondent <- runQuery pool $ R.getRespondent $ TL.toStrict respondentKey
        case maybeRespondent of
          Nothing -> W.html $ renderHtml $ renderPage Modes.WrongRespondent
          Just respondent -> W.html $ renderHtml $ renderPage (Modes.Filling respondent)

wrongRespondentHandler :: Action
wrongRespondentHandler = W.html $ renderHtml $ renderPage Modes.WrongRespondent

saveHandler :: PGPool -> Action
saveHandler pool = do
  ps <- W.params
  let maybeRespondentKey = lookup (TL.fromStrict respondentKeyFieldName) ps
  case maybeRespondentKey of
    Nothing -> W.text "No respondent key"
    Just respondentKey -> do
      maybeRespondent <- runQuery pool $ R.getRespondent $ TL.toStrict respondentKey
      case maybeRespondent of
        Nothing -> W.text "No respondent key"
        Just respondent -> do
          let fieldValues = map (getValue ps) (getFieldInfos Structure.formItems)
          mapM_ (storeValue respondent) fieldValues
          W.text "Data saved"
  where
    getValue :: [W.Param] -> FieldInfo -> FieldValue
    getValue ps (name1, text1) = (name1, text1, lookup name1 ps)
    storeValue :: R.Respondent -> FieldValue -> Action
    storeValue respondent (name1, text1, value1) = do
      resId <- runQuery pool $ resultId respondent $ TL.toStrict name1
      _ <- if resId == 0 then
        runQuery pool $ insertResult respondent (TL.toStrict name1) (TL.toStrict <$> text1) (TL.toStrict <$> value1)
      else
        runQuery pool $ updateResult respondent (TL.toStrict name1) (TL.toStrict <$> value1)
      _ <- runQuery pool $ R.updateSubmission respondent
      return ()


submitHandler :: PGPool -> Action
submitHandler pool = do
  ps <- W.params
  let maybeRespondentKey = lookup (TL.fromStrict respondentKeyFieldName) ps
  case maybeRespondentKey of
    Nothing -> W.redirect $ TL.fromStrict baseURL <> "wrong"
    Just respondentKey -> do
      maybeRespondent <- runQuery pool $ R.getRespondent $ TL.toStrict respondentKey
      case maybeRespondent of
        Nothing -> W.redirect $ TL.fromStrict baseURL <> "wrong"
        Just respondent -> do
          let fieldValues = map (getValue ps) (getFieldInfos Structure.formItems)
          mapM_ (storeValue respondent) fieldValues
          W.redirect $ TL.fromStrict baseURL <> "submitted"
  where
    getValue :: [W.Param] -> FieldInfo -> FieldValue
    getValue ps (name1, text1) = (name1, text1, lookup name1 ps)
    storeValue :: R.Respondent -> FieldValue -> Action
    storeValue respondent (name1, text1, value1) = do
      resId <- runQuery pool $ resultId respondent $ TL.toStrict name1
      _ <- if resId == 0 then
        runQuery pool $ insertResult respondent (TL.toStrict name1) (TL.toStrict <$> text1) (TL.toStrict <$> value1)
      else
        runQuery pool $ updateResult respondent (TL.toStrict name1) (TL.toStrict <$> value1)
      _ <- runQuery pool $ R.updateSubmission respondent
      return ()

submittedHandler :: Action
submittedHandler =  W.html $ renderHtml $ renderPage Modes.Submitted

getDataHandler :: PGPool -> Action
getDataHandler pool = do
  ps <- W.params
  let maybeRespondentKey = lookup (TL.fromStrict respondentKeyFieldName) ps
  case maybeRespondentKey of
    Nothing -> W.text ""
    Just respondentKey -> do
      formData <- runQuery pool $ getResultsForRespondent $ TL.toStrict respondentKey
      W.text $ TL.pack $ show $ values2Data formData
