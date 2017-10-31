{-# LANGUAGE CPP, OverloadedStrings #-}

module Bridge where

import Data.Char (toLower)
import Data.Monoid ((<>))

#ifndef __HASTE__
type JSString = String
toJSString :: String -> JSString
toJSString = id
#else
import Haste
#endif

data ClientAction
  = SavePlan
  deriving (Show)

infoBarId :: String
infoBarId = "info-bar"

formId :: String
formId = "m_questionnaire_form"

toFnName :: ClientAction -> String
toFnName action = let s = show action in
  [toLower (head s)] <> tail s

call0 :: ClientAction -> JSString
call0 action = toJSString $ "Haste['" ++ toFnName action ++ "']($(this))"

call1 :: ClientAction -> String -> JSString
call1 action param = toJSString $ "Haste['" ++ toFnName action ++ "']($(this)," ++ param ++ ")"

