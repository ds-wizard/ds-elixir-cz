{-# LANGUAGE OverloadedStrings, NamedFieldPuns #-}

module DiagramDecorator
(
  tinkerDiagSvgRaw
, tinkerDiagSvgPrimary
, tinkerDiagSvgSecondary
, tinkerDiagSvgPublic
, tinkerDiagSvgProducer
, tinkerDiagSvgExpert
, tinkerDiagSvgConsumer
, tinkerDiagSvgCurator
, tinkerDiagSvgCustodian
, tinkerDiagSvgSteward
, tinkerDiagSvgManager
, tinkerDiagSvgInvestigator
, tinkerDiagramForChapterElement
, tinkerDiagramForElement
, tinkerDiagramForElementBlur
) where

import Prelude
import Data.Monoid ((<>))

import FormEngine.JQuery
import FormEngine.FormItem (tag2Text)
import FormEngine.FormElement.FormElement as Element
import FormEngine.FormElement.Identifiers
import FormEngine.FormContext

highlightCol :: String
highlightCol = "#FBB48F"

lowlightCol :: String
lowlightCol = "white"

tinkerDiagramForChapterElement :: FormElement -> IO ()
tinkerDiagramForChapterElement chapterElem = 
  case elementId chapterElem  of
    "0" -> tinkerDiag0 diagId
    "1" -> tinkerDiag1 diagId
    "2" -> tinkerDiag2 diagId
    "3" -> tinkerDiag3 diagId
    "4" -> tinkerDiag4 diagId
    "5" -> tinkerDiag5 diagId
    "6" -> tinkerDiag6 diagId
    "7" -> tinkerDiag7 diagId
    _ -> return ()
  where diagId = diagramId chapterElem

highlightElem :: ElementSelector -> ElementSelector -> IO ()
highlightElem elemId diagId = do
  --dumptIO $ "hi" <> show (diagId, elemId)
  diagJq <- select $ "#" <> diagId
  elemJq <- selectSVG ("#" <> elemId) diagJq
  _ <- setCss "fill" highlightCol elemJq
  return ()

lowlightElem :: ElementSelector -> ElementSelector -> IO ()
lowlightElem elemId diagId = do
  --dumptIO $ "lo" <> show (diagId, elemId)
  diagJq <- select $ "#" <> diagId
  elemJq <- selectSVG ("#" <> elemId) diagJq
  _ <- setCss "fill" lowlightCol elemJq
  return ()

tinkerDiagSvgRaw :: Handler
tinkerDiagSvgRaw _ = do
  highlightElem "box_1" "svg_raw"
  highlightElem "arrow_1_2" "svg_raw"
  highlightElem "arrow_1_4" "svg_raw"
  highlightElem "box_4_3" "svg_raw"

tinkerDiagSvgPrimary :: Handler
tinkerDiagSvgPrimary _ = do
  highlightElem "box_2" "svg_primary"
  highlightElem "box_4_2" "svg_secondary"
  highlightElem "arrow_2_3" "svg_primary"
  highlightElem "arrow_2_4" "svg_primary"

tinkerDiagSvgSecondary :: Handler
tinkerDiagSvgSecondary _ = do
  highlightElem "box_3" "svg_secondary"
  highlightElem "box_4_1" "svg_secondary"
  highlightElem "arrow_H_3" "svg_secondary"
  highlightElem "arrow_3_4" "svg_secondary"

tinkerDiagSvgPublic :: Handler
tinkerDiagSvgPublic _ = do
  highlightElem "arrow_H_3" "svg_public"

tinkerDiagSvgProducer :: Handler
tinkerDiagSvgProducer _ = do
  highlightElem "box_1" "svg_producer"

tinkerDiagSvgExpert :: Handler
tinkerDiagSvgExpert _ = do
  highlightElem "box_2" "svg_expert"
  highlightElem "box_4_1" "svg_expert"

tinkerDiagSvgConsumer :: Handler
tinkerDiagSvgConsumer _ = do
  highlightElem "box_3" "svg_consumer"

tinkerDiagSvgCurator :: Handler
tinkerDiagSvgCurator _ = do
  highlightElem "box_2" "svg_curator"
  highlightElem "box_3" "svg_curator"
  highlightElem "box_4_1" "svg_curator"
  highlightElem "box_5_i" "svg_curator"
  highlightElem "box_5_e" "svg_curator"
  highlightElem "box_6" "svg_curator"

tinkerDiagSvgCustodian :: Handler
tinkerDiagSvgCustodian _ = do
  highlightElem "box_4_1" "svg_custodian"
  highlightElem "box_5_i" "svg_custodian"
  highlightElem "box_5_e" "svg_custodian"

tinkerDiagSvgSteward :: Handler
tinkerDiagSvgSteward _ = do
  highlightElem "box_1" "svg_steward"
  highlightElem "box_2" "svg_steward"
  highlightElem "box_3" "svg_steward"
  highlightElem "box_4_1" "svg_steward"
  highlightElem "box_5_i" "svg_steward"
  highlightElem "box_5_e" "svg_steward"
  highlightElem "box_6" "svg_steward"

tinkerDiagSvgManager :: Handler
tinkerDiagSvgManager _ = do
  highlightElem "box_1" "svg_manager"
  highlightElem "box_2" "svg_manager"
  highlightElem "box_4_1" "svg_manager"
  highlightElem "box_5_i" "svg_manager"
  highlightElem "box_5_e" "svg_manager"
  highlightElem "box_6" "svg_manager"

tinkerDiagSvgInvestigator :: Handler
tinkerDiagSvgInvestigator _ = do
  highlightElem "institution_box" "svg_investigator"

tinkerDiag0 :: ElementSelector -> IO ()
tinkerDiag0 diagId = do
  highlightElem "institution_box" diagId
  return ()
  
tinkerDiag1 :: ElementSelector -> IO ()
tinkerDiag1 diagId = do
  highlightElem "box_1" diagId
  return ()
  
tinkerDiag2 :: ElementSelector -> IO ()
tinkerDiag2 diagId = do
  highlightElem "box_2" diagId
  return ()
  
tinkerDiag3 :: ElementSelector -> IO ()
tinkerDiag3 diagId = do
  highlightElem "box_3" diagId
  return ()
  
tinkerDiag4 :: ElementSelector -> IO ()
tinkerDiag4 diagId = do
  highlightElem "box_4_1" diagId
  return ()
  
tinkerDiag5 :: ElementSelector -> IO ()
tinkerDiag5 diagId = do
  highlightElem "box_5_i" diagId
  highlightElem "box_5_e" diagId
  return ()
  
tinkerDiag6 :: ElementSelector -> IO ()
tinkerDiag6 diagId = do
  highlightElem "box_6" diagId
  return ()
  
tinkerDiag7 :: ElementSelector -> IO ()
tinkerDiag7 _ = return ()

tinkerDiagramForElement :: FormElement -> FormContext -> IO ()
tinkerDiagramForElement element _ = let
  ts = fmap tag2Text (Element.tags element)
  in do
    mapM_ (flip highlightElem $ diagramId element) ts
    return ()

tinkerDiagramForElementBlur :: FormElement -> FormContext -> IO ()
tinkerDiagramForElementBlur element _ = let
  ts = fmap tag2Text (Element.tags element)
  in do
    mapM_ (flip lowlightElem $ diagramId element) ts
    return ()

