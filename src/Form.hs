{-# LANGUAGE OverloadedStrings #-}

module Form where

import           Prelude
import           Data.Monoid ((<>))

import           FormEngine.JQuery as JQ
import           FormEngine.FormItem
import           FormEngine.FormElement.FormElement as E
import           FormEngine.FormElement.Rendering
import           FormEngine.FormElement.Identifiers
import           FormEngine.FormElement.Tabs
import           FormEngine.FormContext
import           FormEngine.Functionality (emptyElemBehaviour)
import           DiagramDecorator
import           Config.Config (staticURL)
--import Haste.DOM

chapterDiagLoadHandler :: FormElement -> Handler
chapterDiagLoadHandler chapterElem _ =
  --  resizeDescriptions
  tinkerDiagramForChapterElement chapterElem

generateQuestionnaire :: [FormElement] -> IO ()
generateQuestionnaire tabs = do
  formJq <- select "#m_questionnaire_form"
  let allTabs = aboutTab : tabs
  _ <- renderTabGroup allTabs (aboutTabPaneJq : tabsContentsJq tabs) formJq
  _ <- selectTab 0 allTabs
  fireClicks
  where
    tabsContentsJq :: [FormElement] -> [IO JQuery]
    tabsContentsJq = map makePaneJq
      where
        makePaneJq :: FormElement -> IO JQuery
        makePaneJq tab =
          select "<div class='main-pane'></div>"
          >>= makeFormSubPane
          >>= makeDescSubPane
          where
            makeFormSubPane :: JQuery -> IO JQuery
            makeFormSubPane jq =
              appendT "<div class='form-subpane'>" jq
              >>= inside
              >>= foldElements (E.children tab) formContext emptyElemBehaviour
              { focusAction = Just tinkerDiagramForElement
              , blurAction = Just tinkerDiagramForElementBlur
              , detailsFunc = Nothing
              }
              >>= JQ.parent
              where
                formContext = FormContext
                  { allElems = tabs
                  , validImg = "<img class='validity-flag' src='" <> staticURL <> "/img/valid.png'/>"
                  , invalidImg = "<img class='validity-flag' src='" <> staticURL <> "/img/invalid.png'/>"
                  , addImg = "<img alt='add' class='button-add' src='" <> staticURL <> "img/add.png'/>"
                  , removeImg = "<img alt='remove' class='button-add' src='" <> staticURL <> "img/remove.png'/>"
                  }
            makeDescSubPane :: JQuery -> IO JQuery
            makeDescSubPane jq =
              appendT "<div class='desc-subpane'>" jq >>=
              setAttrInside "id" (descSubpaneId tab) >>=
              inside >>=
              loadDiagram
              >>= appendT "<p class='long-desc'>" >>=
              setAttrInside "id" (descSubpaneParagraphId tab)
              >>= inside
              >>= appendT ("<img src='" <> staticURL <> "/img/hint-icon.png' style='margin-right: 5px;'>")
              >>= appendT "<span/>"
              >>= JQ.parent
              >>= JQ.parent
              where
                loadDiagram :: JQuery -> IO JQuery
                loadDiagram jq1 =
                  setHtml
                    "<object class='svg-help' href='http://caniuse.com/#feat=svg' data='/static/img/data_process.svg' type='image/svg+xml'><br>"
                    jq1
                  >>= setAttrInside "id" (diagramId tab)
                  >>= setLoadHandler (chapterDiagLoadHandler tab)
    fireClicks :: IO ()
    fireClicks = do
      _ <- select "input:checked" >>= click >>= click
      _ <- select "input" >>= mouseleave
      _ <- select "textarea" >>= mouseleave
      _ <- select "select" >>= mouseleave
      return ()

aboutTab :: FormElement
aboutTab = ChapterElem
  { chfi = Chapter
    { chDescriptor = defaultFIDescriptor
      { iLabel = Just "About"
      , iNumbering = Numbering [1000] 0
      }
    , chItems = []
    }
  , chElements = []
  , visited = False
  }

aboutTabPaneJq :: IO JQuery
aboutTabPaneJq = select "\
\  <div>\
\    <p>\
\      This questionnaire aims to collect managerial information about the bioinformatics data space.\
\    </p>\
\    <p>\
\      <strong>Only data where the respondent is the owner are subject of the questionnaires</strong>, i.e. not data produced as a service.\
\    </p>\
\    <p>\
\      Its completion should take no more than 15 minutes. If you do not know exact answer, provide your best qualified guess.\
\    </p>\
\    <p>\
\      For questions please contact <a href='mailto:robert.pergl@fit.cvut.cz'>robert.pergl@fit.cvut.cz</a>.\
\    </p>\
\    <br>\
\    <p style='font-size: 90%; font-style: italic;'>\
\      Version of this questionnaire: v2.2\
\    </p>\
\  </div>\
\ "

