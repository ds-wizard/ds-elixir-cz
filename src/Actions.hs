{-# LANGUAGE OverloadedStrings #-}

module Actions
  ( doExports
  ) where

import Prelude
import Data.Maybe (fromMaybe)
import Haste
import Haste.Foreign
import FormEngine.JQuery

import qualified Bridge as B

doExports :: IO ()
doExports = doExport B.SavePlan savePlan

doExport :: (ToAny a, FFI a) => B.ClientAction -> a -> IO ()
doExport action = export (toJSString  $ B.toFnName action)

showMessage :: String -> JQuery -> IO ()
showMessage msg barJq = do
  _ <- appearJq barJq >>= setHtml msg
  _ <- setTimer (Once 3000) (do
    _ <- disappearJq barJq >>= setHtml ""
    return ()
    )
  return ()

showInfo :: JQuery -> String -> IO ()
showInfo _ msg = selectById B.infoBarId >>= showMessage msg

savePlan :: JQuery -> IO ()
savePlan jq = do
  form <- selectById B.formId
  ajaxSubmitForm form (showInfo jq . fromMaybe "")

