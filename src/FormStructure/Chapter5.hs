{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Chapter5 (ch5DataAccessibility) where
#ifndef __HASTE__
--import           Data.Text (pack)
#endif
import           FormEngine.FormItem
import           FormStructure.Common

ch5DataAccessibility :: FormItem
ch5DataAccessibility = Chapter
  { chDescriptor = defaultFIDescriptor { iLabel = Just "5.Accessibility " }
  , chItems = [provide, remark]
  }
  where
    provide :: FormItem
    provide = ChoiceFI
      { chfiDescriptor = defaultFIDescriptor
        { iLabel = Just "Do you provide data accessibility for external parties?"
        , iMandatory = True
        }
      , chfiAvailableOptions = [DetailedOption NoNumbering "Yes" [how], SimpleOption "No"]
      }
      where
        how :: FormItem
        how = SimpleGroup
          { sgDescriptor = defaultFIDescriptor
            { iLabel = Just "Accessibility details"
            , iMandatory = True
            }
          , sgLevel = 1
          , sgItems = [ TextFI
                        { tfiDescriptor = defaultFIDescriptor
                          { iLabel = Just "How do you make your data accessible?"
                          , iShortDescription = Just
                                                  "For inspiration, click the red box in the figure"
                          , iMandatory = True
                          }
                        }
                      , TextFI
                        { tfiDescriptor = defaultFIDescriptor
                          { iLabel = Just "Links to your services"
                          , iShortDescription = Just
                                                  "URLs to web pages / data source or other accessibility link"
                          , iMandatory = True
                          }
                        }
                      ]
          }