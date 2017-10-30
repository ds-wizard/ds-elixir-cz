{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Chapter4 (ch4DataStorage) where

#ifndef __HASTE__
--import           Data.Text.Lazy (pack)
#endif

import           FormEngine.FormItem
import           FormStructure.Common

ch4DataStorage :: FormItem
ch4DataStorage = Chapter
  { chDescriptor = defaultFIDescriptor { iLabel = Just "4.Storage " }
  , chItems = [volumes, providers, remark]
  }
  where
    volumes :: FormItem
    volumes = SimpleGroup
      { sgDescriptor = defaultFIDescriptor
        { iLabel = Just "Data volumes"
        , iShortDescription = Just
                                "Just scientic data volumes (without backups and scratch/tmp) are in question."
        , iMandatory = True
        }
      , sgLevel = 0
      , sgItems = [ NumberFI
                    { nfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Total volume produced in 2016"
                      , iIdent = Just "total-volume"
                      , iRules = [ReadOnlyRule]
                      }
                    , nfiUnit = SingleUnit "TB"
                    }
                  , NumberFI
                    { nfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Total volume of data stored at the end of 2016"
                      , iMandatory = True
                      }
                    , nfiUnit = MultipleUnit ["MB", "GB", "TB", "PB"]
                    }
                  , NumberFI
                    { nfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Total volume of backups"
                      , iMandatory = True
                      }
                    , nfiUnit = MultipleUnit ["MB", "GB", "TB", "PB"]
                    }
                  ]
      }
    providers :: FormItem
    providers = SimpleGroup
      { sgDescriptor = defaultFIDescriptor
        { iLabel = Just "Storage providers"
        , iMandatory = True
        }
      , sgLevel = 0
      , sgItems = [ NumberFI
                    { nfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Group's local"
                      , iIdent = Just "storage-provider-group"
                      , iRules = [storageSumRule, NumValueRule (\n -> n >= 0 && n <= 100)]
                      , iMandatory = True
                      }
                    , nfiUnit = SingleUnit "%"
                    }
                  , NumberFI
                    { nfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Institutional"
                      , iIdent = Just "storage-provider-institutional"
                      , iRules = [storageSumRule, NumValueRule (\n -> n >= 0 && n <= 100)]
                      , iMandatory = True
                      }
                    , nfiUnit = SingleUnit "%"
                    }
                  , NumberFI
                    { nfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "External Provider"
                      , iIdent = Just "storage-provider-external"
                      , iRules = [storageSumRule, NumValueRule (\n -> n >= 0 && n <= 100)]
                      , iMandatory = True
                      }
                    , nfiUnit = SingleUnit "%"
                    }
                  , NumberFI
                    { nfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Sum"
                      , iIdent = Just "storage-providers-sum"
                      , iRules = [ReadOnlyRule, NumValueRule (== 100)]
                      , iMandatory = True
                      }
                    , nfiUnit = SingleUnit "%"
                    }
                  ]
      }
      where
        storageSumRule :: FormRule
        storageSumRule = SumRule
                           [ "storage-provider-group"
                           , "storage-provider-institutional"
                           , "storage-provider-external"
                           ]
                           "storage-providers-sum"