{-# LANGUAGE OverloadedStrings #-}

module Model.Respondent where

import           Data.Text (Text, pack)
import           Data.Maybe (fromMaybe)
import           Control.Monad.Trans
import qualified Database.PostgreSQL.Simple as PG
import           Database.PostgreSQL.Simple.FromRow
import qualified Data.Time.Clock as DTC

data Respondent =
       Respondent
         { id :: Int
         , name :: Text
         , key :: Text
         , accessed :: Maybe DTC.UTCTime
         , finished :: Maybe DTC.UTCTime
         }
  deriving Show

instance FromRow Respondent where
  fromRow = Respondent <$> field <*> field <*> field <*> field <*> field

updateAccess :: Respondent -> PG.Connection -> IO Int
updateAccess respondent conn = do
  ts <- liftIO DTC.getCurrentTime
  r <- PG.execute conn "UPDATE \"Respondents\" SET accessed = ?\
                     \ WHERE id = ?" (ts, Model.Respondent.id respondent)
  return (fromIntegral r)

updateSubmission :: Respondent -> PG.Connection -> IO Int
updateSubmission respondent conn = do
  ts <- liftIO DTC.getCurrentTime
  r <- PG.execute conn "UPDATE \"Respondents\" SET finished = ?\
                     \ WHERE id = ?" (ts, Model.Respondent.id respondent)
  return (fromIntegral r)

getRespondent :: Text -> PG.Connection -> IO (Maybe Respondent)
getRespondent key conn = do
  results <- PG.query conn
               "SELECT \
                \    id, \
                \    name, \
                \    key, \
                \    accessed, \
                \    finished \
                \FROM \
                \    \"Respondents\" \
                \WHERE \
                \    key = ?"
               (PG.Only key)
  let r = results :: [Respondent]
  if null r
    then return Nothing
    else do
      let respondent = head r
      updateAccess respondent conn
      return $ Just respondent

submissionInfo :: Respondent -> Text
submissionInfo respondent = fromMaybe "never" ((pack . show) <$> finished respondent)
