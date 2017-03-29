{-# LANGUAGE OverloadedStrings #-}

module FormStructure.Submit (submitForm) where

import           FormEngine.FormItem

submitForm :: FormItem
submitForm = Chapter
  { chDescriptor = defaultFIDescriptor { iLabel = Just "Finish" }
  , chItems = [saveButton]
  }
  where
    saveButton :: FormItem
    saveButton = SaveButtonFI
      { sviDescriptor = defaultFIDescriptor
        { iShortDescription = Just "Save your answers."
        , iMandatory = True
        }
      }
--    submitButton :: FormItem
--    submitButton = SubmitButtonFI
--      { sbiDescriptor = defaultFIDescriptor
--        , iShortDescription = Just "Finish and submit the answers."
--        , iMandatory = True
--        }
--      }