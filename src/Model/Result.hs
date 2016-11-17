{-# LANGUAGE OverloadedStrings #-}

module Model.Result where

import           Data.Text (Text, pack)
import           Data.Maybe (fromMaybe)
import           Data.Int (Int64)
import qualified Database.PostgreSQL.Simple as PG
import           Database.PostgreSQL.Simple.FromRow

import           FormEngine.FormItem
import           FormEngine.FormData
import           Model.Respondent as R

data Result =
       Result
         { id :: Int
         , respondentId :: Int
         , name :: Text
         , text :: Maybe Text
         , value :: Maybe Text
         }
  deriving Show

instance FromRow Result where
  fromRow = Result <$> field <*> field <*> field <*> field <*> field

resultId :: Respondent -> Text -> PG.Connection -> IO Int
resultId respondent name conn = do
  r <- PG.query conn
        "SELECT id FROM \"Results\" WHERE respondent_id = ? AND name = ?"
        (R.id respondent, name) :: IO [PG.Only Int] 
  let x =
        case r of
          (f:_) -> f
          []    -> PG.Only 0
  let (PG.Only i) = x
  return i

updateResult :: Respondent -> Text -> Maybe Text -> PG.Connection -> IO Int
updateResult respondent name value conn = do
  r <- PG.execute conn "UPDATE \"Results\" SET value = ?\
                     \ WHERE name = ? AND respondent_id = ?" (value, name, R.id respondent) 
  return (fromIntegral r)

insertResult :: Respondent -> Text -> Maybe Text -> Maybe Text -> PG.Connection -> IO Int
insertResult respondent name text value conn = do
  r <- PG.query conn "INSERT INTO \"Results\" (respondent_id, name, text, value) VALUES (?, ?, ?, ?) RETURNING id"
         (R.id respondent, name, text, value) :: IO [PG.Only Int]
  let x =
        case r of
          (f:_) -> f
          []    -> PG.Only 0
  let (PG.Only i) = x
  return i

getResultsForRespondent :: Text -> PG.Connection -> IO [FieldValue]
getResultsForRespondent respondentKey conn = PG.query conn
                                          "SELECT name, text, value FROM \"Results\" WHERE respondent_id = (SELECT id from \"Respondents\" WHERE key=?)"
                                          (PG.Only respondentKey)
