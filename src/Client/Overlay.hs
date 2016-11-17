{-# LANGUAGE OverloadedStrings #-}

module Overlay (overlay) where

import Prelude

import FormEngine.JQuery 

setBoxTopMargin :: JQuery -> IO JQuery
setBoxTopMargin o = do
  box <- findSelector "div" o
  top <- select "body" >>= getScrollTop
  setCss "margin-top" (show $ top + 25) box

setOverlaySize :: JQuery -> IO JQuery
setOverlaySize o = do
  h <- select "body" >>= getHeight 
  setHeight h o

overlaySwitch :: JQuery -> IO JQuery
overlaySwitch o = do
  v <- getCss "visibility" o
  if v == "visible" then 
    hideJq o
  else
    showJq o

overlay :: String -> IO JQuery
overlay elemId = select ("#" ++ elemId) >>= setOverlaySize >>= overlaySwitch >>= setBoxTopMargin
  
