{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Common where
#ifndef __HASTE__
import           Data.Text (pack)
#endif 
import           FormEngine.FormItem

cost :: FormItem
cost =
  NumberFI
    { nfiDescriptor = FIDescriptor
      { iLabel = Just "Cost for year 2015"
      , iNumbering = NoNumbering
      , iIdent = Nothing
      , iTags = []
      , iShortDescription = Nothing
      , iLongDescription = Nothing
      , iLink = Nothing
      , iRules = []
      , iMandatory = False
      }
    , nfiUnit = SingleUnit "thousand EUR"
    }

remark :: FormItem
remark = SimpleGroup
  { sgDescriptor = FIDescriptor
    { iLabel = Just "Other"
    , iNumbering = NoNumbering
    , iIdent = Nothing
    , iTags = []
    , iShortDescription = Nothing
    , iLongDescription = Nothing
    , iLink = Nothing
    , iRules = []
    , iMandatory = True
    }
  , sgLevel = 0
  , sgItems = [ TextFI
                { tfiDescriptor = FIDescriptor
                  { iLabel = Just "Your comments"
                  , iNumbering = NoNumbering
                  , iIdent = Nothing
                  , iTags = []
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = []
                  , iMandatory = False
                  }
                }
              ]
  }

xhow :: FormItem
xhow = TextFI
  { tfiDescriptor = FIDescriptor
    { iLabel = Just "How?"
    , iNumbering = NoNumbering
    , iIdent = Nothing
    , iTags = []
    , iShortDescription = Nothing
    , iLongDescription = Nothing
    , iLink = Nothing
    , iRules = []
    , iMandatory = True
    }
  }

totalSum :: FormRule
totalSum = SumTBsRule ["raw-volume-genomics", "raw-volume-proteomics", "raw-volume-others", "prim-volume", "sec-volume"]
                        "total-volume"
