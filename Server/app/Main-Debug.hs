{-# LANGUAGE OverloadedStrings #-}

import           FormItem
import           FormStructure.FormStructure as Structure
import           FormData
import           Text.Show.Pretty
import           Data.ByteString.Char8 (ByteString, pack)
import           Debug.Hood.Observe

main :: IO ()
main = do
  let fieldInfos = getFieldInfos Structure.formItems
  runO $ putStrLn $ ppShow $ fieldInfos
  return ()
