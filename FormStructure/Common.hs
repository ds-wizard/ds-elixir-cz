{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Common where

#ifndef __HASTE__
--import           Data.Text.Lazy (pack)
#endif

import           FormEngine.FormItem

cost :: FormItem
cost =
  NumberFI
    { nfiDescriptor = defaultFIDescriptor { iLabel = Just "Cost for year 2016" }
    , nfiUnit = SingleUnit "thousand EUR"
    }

remark :: FormItem
remark = SimpleGroup
  { sgDescriptor = defaultFIDescriptor { iLabel = Just "Other" }
  , sgLevel = 0
  , sgItems = [ TextFI { tfiDescriptor = defaultFIDescriptor { iLabel = Just "Your comments" } } ]
  }

xhow :: FormItem
xhow = TextFI { tfiDescriptor = defaultFIDescriptor { iLabel = Just "How?" } }

totalSum :: FormRule
totalSum = SumTBsRule ["raw-volume-genomics", "raw-volume-proteomics", "raw-volume-others", "prim-volume", "sec-volume"]
                        "total-volume"
