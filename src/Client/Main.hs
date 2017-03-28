{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Prelude
import           Control.Monad
import           Data.Maybe (fromMaybe, isNothing, catMaybes)
import           Text.Read (readMaybe)

import           Haste
import           Haste.JSString (pack)
import           Haste.Ajax
import           Haste.Foreign (export)


import           FormStructure.FormStructure as Structure
import           Overlay
import           Page
import           FormEngine.JQuery
import           FormEngine.FormData
import           FormEngine.FormElement.FormElement as Element
import           FormEngine.FormElement.Identifiers
import           Form
--import           About
import           DiagramDecorator

scrollHandler :: [FormElement] -> Handler
scrollHandler tabGroup _ = do
  let paneSels = getPanesSelectors tabGroup
  visiblePaneSels <- filterM (select >=> isVisible) paneSels
  unless (null visiblePaneSels) $ do
    visiblePane <- select (head visiblePaneSels)
    windowTop <- getWindow >>= getScrollTop
    divTop <- getTop visiblePane
    let delta = windowTop - divTop
    when (delta > 0) $ do
      _ <- setCss "margin-top" (toPx delta) visiblePane
      return ()
  where
   getPanesSelectors :: [FormElement] -> [ElementSelector]
   getPanesSelectors = map (("#" ++) . descSubpaneId)

resizeHandler :: Handler
resizeHandler _ = do
  let paneSel = ".desc-subpane"
  winWidth <- getWindow >>= getWidth
  _ <- select paneSel >>= setWidth (winWidth - 790)
  _ <- select ".svg-help" >>= setWidth (winWidth - 795)
  return ()

getRespondentKey :: IO String
getRespondentKey = select "#respondent_key_field" >>= getVal

main :: IO ()
main = ready $ do
  export "overlay" overlay
  export "toVision" toVision
  export "toAction" toAction
  export "toLifecycle" toLifecycle
  export "toData" toData
  export "toRoles" toRoles
  export "toMQuestionnaire" toMQuestionnaire
  export "toTQuestionnaire" toTQuestionnaire
  _ <- select "#svg_raw" >>= onLoad tinkerDiagSvgRaw
  _ <- select "#svg_primary" >>= onLoad tinkerDiagSvgPrimary
  _ <- select "#svg_secondary" >>= onLoad tinkerDiagSvgSecondary
  _ <- select "#svg_public" >>= onLoad tinkerDiagSvgPublic
  _ <- select "#svg_producer" >>= onLoad tinkerDiagSvgProducer
  _ <- select "#svg_expert" >>= onLoad tinkerDiagSvgExpert
  _ <- select "#svg_consumer" >>= onLoad tinkerDiagSvgConsumer
  _ <- select "#svg_curator" >>= onLoad tinkerDiagSvgCurator
  _ <- select "#svg_custodian" >>= onLoad tinkerDiagSvgCustodian
  _ <- select "#svg_steward" >>= onLoad tinkerDiagSvgSteward
  _ <- select "#svg_manager" >>= onLoad tinkerDiagSvgManager
  _ <- select "#svg_investigator" >>= onLoad tinkerDiagSvgInvestigator
  respondentKey <- getRespondentKey
  ajaxRequest POST "api/getData" [("respondent_key" :: JSString, pack respondentKey :: JSString)] buildQuestionnaire
    where
    buildQuestionnaire :: Maybe String -> IO ()
    buildQuestionnaire maybeDataString = do
     -- dumptIO (fromMaybe "" maybeDataString)
      let maybeFormData = readMaybe (fromMaybe "" maybeDataString) :: Maybe FormData
      let tabMaybes = map (Element.makeChapter maybeFormData) Structure.formItems
      if any isNothing tabMaybes then do
        errorIO "Error generating tabs"
        return ()
      else do
        let tabs = catMaybes tabMaybes
        time "Generate"
        generateQuestionnaire tabs
        timeEnd "Generate"
        _ <- getWindow >>= onScroll (scrollHandler tabs)
        _ <- getWindow >>= onResize resizeHandler
        _ <- getWindow >>= resize
        toVision ()
        return ()


