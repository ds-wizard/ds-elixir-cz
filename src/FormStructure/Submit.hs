{-# LANGUAGE OverloadedStrings #-}

module FormStructure.Submit (submitForm) where

import           FormEngine.FormItem

submitForm :: FormItem
submitForm = Chapter
  { chDescriptor = FIDescriptor
    { iNumbering = NoNumbering
    , iLabel = Just "Finish"
    , iIdent = Nothing
    , iTags = []
    , iShortDescription = Nothing
    , iLongDescription = Nothing
    , iLink = Nothing
    , iRules = []
    , iMandatory = False
    }
  , chItems = [saveButton]
  }
  where
    saveButton :: FormItem
    saveButton = SaveButtonFI
      { sviDescriptor = FIDescriptor
        { iNumbering = NoNumbering
        , iLabel = Nothing
        , iIdent = Nothing
        , iTags = []
        , iShortDescription = Just "Save your answers."
        , iLongDescription = Nothing
        , iLink = Nothing
        , iRules = []
        , iMandatory = True
        }
      }
--    submitButton :: FormItem
--    submitButton = SubmitButtonFI
--      { sbiDescriptor = FIDescriptor
--        { iNumbering = NoNumbering
--        , iLabel = Nothing
--        , iIdent = Nothing
--        , iTags = []
--        , iShortDescription = Just "Finish and submit the answers."
--        , iLongDescription = Nothing
--        , iLink = Nothing
--        , iRules = []
--        , iMandatory = True
--        }
--      }