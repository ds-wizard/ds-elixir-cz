{-# LANGUAGE OverloadedStrings #-}

module Main where

import Haste.DOM
import           JQuery

main :: IO ()
main = ready $ do
  maybeForm <- elemById "m_questionnaire_form"
  case maybeForm of
    Nothing -> dumptIO "no form selected"
    Just form -> do
      time "newElem"
      mapM_ (\i -> do e <- newElem "p"; appendChild form e) [1..100] 
      timeEnd "newElem"
      dumptIO "end"
  return ()
