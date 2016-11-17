module Config.Server.Config where

import           Web.Spock.Shared
import qualified Database.PostgreSQL.Simple as PG

port :: Int
port = 8000

creds :: PG.ConnectInfo
creds =
    PG.ConnectInfo
        { PG.connectHost     = "localhost"
        , PG.connectPort     = 5432
        , PG.connectUser     = "elixir"
        , PG.connectPassword = "elixir"
        , PG.connectDatabase = "elixir-questionnaire"
        }

poolCfg :: PoolCfg
poolCfg = PoolCfg 50 50 60

pcconn :: ConnBuilder PG.Connection
pcconn = ConnBuilder (PG.connect creds) PG.close poolCfg

dbConn :: PoolOrConn PG.Connection
dbConn = PCConn pcconn 

