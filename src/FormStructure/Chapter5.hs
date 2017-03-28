{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Chapter5 (ch5DataAccessibility) where
#ifndef __HASTE__
--import           Data.Text (pack)
#endif
import           FormEngine.FormItem
import           FormStructure.Common

ch5DataAccessibility :: FormItem
ch5DataAccessibility = Chapter
  { chDescriptor = FIDescriptor
    { iNumbering = NoNumbering
    , iLabel = Just "5.Accessibility "
    , iIdent = Nothing
    , iTags = []
    , iShortDescription = Nothing
    , iLongDescription = Nothing
    , iLink = Nothing
    , iRules = []
    , iMandatory = False
    }
  , chItems = [provide, remark]
  }
  where
    provide :: FormItem
    provide = ChoiceFI
      { chfiDescriptor = FIDescriptor
        { iLabel = Just "Do you provide data accessibility for external parties?"
        , iNumbering = NoNumbering
        , iIdent = Nothing
        , iTags = []
        , iShortDescription = Nothing
        , iLongDescription = Nothing
        , iLink = Nothing
        , iRules = []
        , iMandatory = True
        }
      , chfiAvailableOptions = [DetailedOption NoNumbering "Yes" [how], SimpleOption "No"]
      }
      where
        how :: FormItem
        how = SimpleGroup
          { sgDescriptor = FIDescriptor
            { iLabel = Just "Accessibility details"
            , iNumbering = NoNumbering
            , iIdent = Nothing
            , iTags = []
            , iShortDescription = Nothing
            , iLongDescription = Nothing
            , iLink = Nothing
            , iRules = []
            , iMandatory = True
            }
          , sgLevel = 1
          , sgItems = [ TextFI
                        { tfiDescriptor = FIDescriptor
                          { iLabel = Just "How do you make your data accessible?"
                          , iNumbering = NoNumbering
                          , iIdent = Nothing
                          , iTags = []
                          , iShortDescription = Just
                                                  "For inspiration, click the red box in the figure"
                          , iLongDescription = Nothing
                          , iLink = Nothing
                          , iRules = []
                          , iMandatory = True
                          }
                        }
                      , TextFI
                        { tfiDescriptor = FIDescriptor
                          { iLabel = Just "Links to your services"
                          , iNumbering = NoNumbering
                          , iIdent = Nothing
                          , iTags = []
                          , iShortDescription = Just
                                                  "URLs to web pages / data source or other accessibility link"
                          , iLongDescription = Nothing
                          , iLink = Nothing
                          , iRules = []
                          , iMandatory = True
                          }
                        }
                      ]
          }