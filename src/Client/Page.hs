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
    { chDescriptor = FIDescriptor
      { iLabel = Nothing
      , iNumbering = Numbering [100] 0
      , iIdent = Nothing
      , iTags = []
      , iShortDescription = Nothing
      , iLongDescription = Nothing
      , iLink = Nothing
      , iRules = []
      , iMandatory = False
      }
    , chItems = []
    }
  , chElements = []
  , visited = False
  }

actionTab :: FormElement
actionTab = ChapterElem
  { chfi = Chapter
    { chDescriptor = FIDescriptor
      { iLabel = Nothing
      , iNumbering = Numbering [200] 0
      , iIdent = Nothing
      , iTags = []
      , iShortDescription = Nothing
      , iLongDescription = Nothing
      , iLink = Nothing
      , iRules = []
      , iMandatory = False
      }
    , chItems = []
    }
  , chElements = []
  , visited = False
  }

lifecycleTab :: FormElement
lifecycleTab = ChapterElem
  { chfi = Chapter
    { chDescriptor = FIDescriptor
      { iLabel = Nothing
      , iNumbering = Numbering [300] 0
      , iIdent = Nothing
      , iTags = []
      , iShortDescription = Nothing
      , iLongDescription = Nothing
      , iLink = Nothing
      , iRules = []
      , iMandatory = False
      }
    , chItems = []
    }
  , chElements = []
  , visited = False
  }

dataTab :: FormElement
dataTab = ChapterElem
  { chfi = Chapter
    { chDescriptor = FIDescriptor
      { iLabel = Nothing
      , iNumbering = Numbering [400] 0
      , iIdent = Nothing
      , iTags = []
      , iShortDescription = Nothing
      , iLongDescription = Nothing
      , iLink = Nothing
      , iRules = []
      , iMandatory = False
      }
    , chItems = []
    }
  , chElements = []
  , visited = False
  }

rolesTab :: FormElement
rolesTab = ChapterElem
  { chfi = Chapter
    { chDescriptor = FIDescriptor
      { iLabel = Nothing
      , iNumbering = Numbering [500] 0
      , iIdent = Nothing
      , iTags = []
      , iShortDescription = Nothing
      , iLongDescription = Nothing
      , iLink = Nothing
      , iRules = []
      , iMandatory = False
      }
    , chItems = []
    }
  , chElements = []
  , visited = False
  }

mQuestionnaireTab :: FormElement
mQuestionnaireTab = ChapterElem
  { chfi = Chapter
    { chDescriptor = FIDescriptor
      { iLabel = Nothing
      , iNumbering = Numbering [600] 0
      , iIdent = Nothing
      , iTags = []
      , iShortDescription = Nothing
      , iLongDescription = Nothing
      , iLink = Nothing
      , iRules = []
      , iMandatory = False
      }
    , chItems = []
    }
  , chElements = []
  , visited = False
  }

tQuestionnaireTab :: FormElement
tQuestionnaireTab = ChapterElem
  { chfi = Chapter
    { chDescriptor = FIDescriptor
      { iLabel = Nothing
      , iNumbering = Numbering [700] 0
      , iIdent = Nothing
      , iTags = []
      , iShortDescription = Nothing
      , iLongDescription = Nothing
      , iLink = Nothing
      , iRules = []
      , iMandatory = False
      }
    , chItems = []
    }
  , chElements = []
  , visited = False
  }

toVision :: () -> IO ()
toVision _ = toTab visionTab pageTabGroup

toAction :: () -> IO ()
toAction _ = toTab actionTab pageTabGroup

toLifecycle :: () -> IO ()
toLifecycle _ = toTab lifecycleTab pageTabGroup

toData :: () -> IO ()
toData _ = toTab dataTab pageTabGroup

toRoles :: () -> IO ()
toRoles _ = toTab rolesTab pageTabGroup

toMQuestionnaire :: () -> IO ()
toMQuestionnaire _ = toTab mQuestionnaireTab pageTabGroup

toTQuestionnaire :: () -> IO ()
toTQuestionnaire _ = toTab tQuestionnaireTab pageTabGroup