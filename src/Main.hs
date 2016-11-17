{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Data.Monoid
import           Control.Monad.IO.Class (MonadIO)
import           Data.Text.Lazy (toStrict, pack)
import           Text.Blaze.Html.Renderer.Text
import           Web.Spock.Safe as W
import           Network.Wai.Middleware.Static as M
import           Network.Wai.Middleware.RequestLogger
import           Data.Pool
import qualified Database.PostgreSQL.Simple as PG

import           Config.Config
import           Config.Server.Config

import           FormStructure.FormStructure as Structure
import           FormEngine.FormItem
import           FormEngine.FormData
import qualified Modes
import           Model.Respondent as R
import           Model.Result as U
import           PageGenerator (renderPage)
--import           Text.Show.Pretty

main :: IO ()
main = do
  --pool <- createPool (cb_createConn pcconn) (cb_destroyConn pcconn)
  --                  (pc_stripes poolCfg) (pc_keepOpenTime poolCfg)
  --                  (pc_resPerStripe poolCfg)
  runSpock port $ spock (defaultSpockCfg Nothing dbConn ()) $ subcomponent "/" $ do -- why the hell the following line does not work?
  --runSpock port $ spock (defaultSpockCfg Nothing dbConn ()) $ subcomponent (W.static (show baseURL)) $ do
    middleware M.static
    middleware logStdoutDev
    get root rootHandler
    get "wrong" wrongRespondentHandler
    post "submit" submitHandler
    get "submitted" submittedHandler
    post "api/getData" getDataHandler

rootHandler :: ActionCtxT ctx (WebStateM PG.Connection b ()) a
rootHandler = do 
    ps <- params
    let maybeRespondentKey = lookup respondentKeyFieldName ps 
    case maybeRespondentKey of
      Nothing -> html $ toStrict $ renderHtml $ renderPage Modes.ReadOnly
      Just respondentKey -> do
        maybeRespondent <- runQuery $ getRespondent respondentKey
        case maybeRespondent of
          Nothing -> html $ toStrict $ renderHtml $ renderPage Modes.WrongRespondent
          Just respondent -> html $ toStrict $ renderHtml $ renderPage (Modes.Filling respondent)

wrongRespondentHandler :: MonadIO m => ActionCtxT ctx m a
wrongRespondentHandler = html $ toStrict $ renderHtml $ renderPage Modes.WrongRespondent

submitHandler :: ActionCtxT ctx (WebStateM PG.Connection b ()) a
submitHandler = do
  ps <- params
  let maybeRespondentKey = lookup respondentKeyFieldName ps
  case maybeRespondentKey of
    Nothing -> redirect $ baseURL <> "wrong"
    Just respondentKey -> do
      maybeRespondent <- runQuery $ getRespondent respondentKey
      case maybeRespondent of
        Nothing -> redirect $ baseURL <> "wrong"
        Just respondent -> do 
          ps <- params
          let fieldValues = map (getValue ps) (getFieldInfos Structure.formItems) 
          mapM_ (storeValue respondent) fieldValues
          redirect $ baseURL <> "submitted"
  where
    getValue ps (name, text) = (name, text, lookup name ps)
    storeValue :: Respondent -> FieldValue -> ActionCtxT ctx (WebStateM PG.Connection b ()) () 
    storeValue respondent (name, text, value) = do
      resId <- runQuery $ resultId respondent name
      if resId == 0 then 
        runQuery $ insertResult respondent name text value 
      else 
        runQuery $ updateResult respondent name value 
      runQuery $ R.updateSubmission respondent
      return ()

submittedHandler :: ActionCtxT ctx (WebStateM PG.Connection b ()) a
submittedHandler =  html $ toStrict $ renderHtml $ renderPage Modes.Submitted

getDataHandler :: ActionCtxT ctx (WebStateM PG.Connection b ()) a
getDataHandler = do
  ps <- params
  let maybeRespondentKey = lookup respondentKeyFieldName ps 
  case maybeRespondentKey of
    Nothing -> W.text ""
    Just respondentKey -> do
      formData <- runQuery $ getResultsForRespondent respondentKey
      W.text $ toStrict $ pack $ show $ values2Data formData
