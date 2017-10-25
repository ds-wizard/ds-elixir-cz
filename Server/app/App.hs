{-# LANGUAGE OverloadedStrings #-}

module App
  ( Action
  , PGPool
  , runQuery
  ) where

import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans (liftIO)
import Data.Pool (Pool, withResource)
import Database.PostgreSQL.Simple (Connection)
import Web.Scotty (ActionM)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

type Action = ActionM ()

type PGPool = Pool Connection

runQuery
  :: MonadIO m
  => Pool Connection -> (Connection -> IO a) -> m a
runQuery pool query = liftIO $ withResource pool query
