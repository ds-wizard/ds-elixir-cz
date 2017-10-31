{-# LANGUAGE RebindableSyntax #-}

module Page (
    pageTabGroup,
    toVision,
    toAction,
    toLifecycle,
    toData,
    toRoles,
    toMQuestionnaire,
    toTQuestionnaire,
    ) where

import           Prelude
import           FormEngine.JQuery

import           FormEngine.FormItem
import           FormEngine.FormElement.FormElement
import           FormEngine.FormElement.Tabs

pageTabGroup :: [FormElement]
pageTabGroup = [ visionTab
               , actionTab
               , lifecycleTab
               , dataTab
               , rolesTab
               , mQuestionnaireTab
               , tQuestionnaireTab
               ]

visionTab :: FormElement
visionTab = ChapterElem
  { chfi = Chapter
    { chDescriptor = defaultFIDescriptor { iNumbering = Numbering [100] 0 }
    , chItems = []
    }
  , chElements = []
  , visited = False
  }

actionTab :: FormElement
actionTab = ChapterElem
  { chfi = Chapter
    { chDescriptor = defaultFIDescriptor { iNumbering = Numbering [200] 0 }
    , chItems = []
    }
  , chElements = []
  , visited = False
  }

lifecycleTab :: FormElement
lifecycleTab = ChapterElem
  { chfi = Chapter
    { chDescriptor = defaultFIDescriptor { iNumbering = Numbering [300] 0 }
    , chItems = []
    }
  , chElements = []
  , visited = False
  }

dataTab :: FormElement
dataTab = ChapterElem
  { chfi = Chapter
    { chDescriptor = defaultFIDescriptor { iNumbering = Numbering [400] 0 }
    , chItems = []
    }
  , chElements = []
  , visited = False
  }

rolesTab :: FormElement
rolesTab = ChapterElem
  { chfi = Chapter
    { chDescriptor = defaultFIDescriptor { iNumbering = Numbering [500] 0 }
    , chItems = []
    }
  , chElements = []
  , visited = False
  }

mQuestionnaireTab :: FormElement
mQuestionnaireTab = ChapterElem
  { chfi = Chapter
    { chDescriptor = defaultFIDescriptor  { iNumbering = Numbering [600] 0 }
    , chItems = []
    }
  , chElements = []
  , visited = False
  }

tQuestionnaireTab :: FormElement
tQuestionnaireTab = ChapterElem
  { chfi = Chapter
    { chDescriptor = defaultFIDescriptor { iNumbering = Numbering [700] 0 }
    , chItems = []
    }
  , chElements = []
  , visited = False
  }

controlPanelId :: String
controlPanelId = "control-panel"

hideControlPanel :: IO ()
hideControlPanel = do
  _ <- selectById controlPanelId >>= disappearJq
  return ()

showControlPanel :: IO ()
showControlPanel = do
  _ <- selectById controlPanelId >>= appearJq
  return ()

toVision :: () -> IO ()
toVision _ = do
  hideControlPanel
  toTab visionTab pageTabGroup

toAction :: () -> IO ()
toAction _ = do
  hideControlPanel
  toTab actionTab pageTabGroup

toLifecycle :: () -> IO ()
toLifecycle _ = do
  hideControlPanel
  toTab lifecycleTab pageTabGroup

toData :: () -> IO ()
toData _ = do
  hideControlPanel
  toTab dataTab pageTabGroup

toRoles :: () -> IO ()
toRoles _ = do
  hideControlPanel
  toTab rolesTab pageTabGroup

toMQuestionnaire :: () -> IO ()
toMQuestionnaire _ = do
  showControlPanel
  toTab mQuestionnaireTab pageTabGroup

toTQuestionnaire :: () -> IO ()
toTQuestionnaire _ = do
  hideControlPanel
  toTab tQuestionnaireTab pageTabGroup