{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Chapter4 (ch4DataStorage) where
#ifndef __HASTE__
--import           Data.Text (pack)
#endif
import           FormEngine.FormItem
import           FormStructure.Common

ch4DataStorage :: FormItem
ch4DataStorage = Chapter
  { chDescriptor = FIDescriptor
    { iNumbering = NoNumbering
    , iLabel = Just "4.Storage "
    , iIdent = Nothing
    , iTags = []
    , iShortDescription = Nothing
    , iLongDescription = Nothing
    , iLink = Nothing
    , iRules = []
    , iMandatory = False
    }
  , chItems = [volumes, providers, remark]
  }
  where
    volumes :: FormItem
    volumes = SimpleGroup
      { sgDescriptor = FIDescriptor
        { iLabel = Just "Data volumes"
        , iShortDescription = Just
                                "Just scientic data volumes (without backups and scratch/tmp) are in question."
        , iNumbering = NoNumbering
        , iIdent = Nothing
        , iTags = []
        , iLongDescription = Nothing
        , iLink = Nothing
        , iRules = []
        , iMandatory = True
        }
      , sgLevel = 0
      , sgItems = [ NumberFI
                    { nfiDescriptor = FIDescriptor
                      { iLabel = Just "Total volume produced in 2015"
                      , iNumbering = NoNumbering
                      , iIdent = Just "total-volume"
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = [ReadOnlyRule]
                      , iMandatory = False
                      }
                    , nfiUnit = SingleUnit "TB"
                    }
                  , NumberFI
                    { nfiDescriptor = FIDescriptor
                      { iLabel = Just "Total volume of data stored at the end of 2015"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = []
                      , iMandatory = True
                      }
                    , nfiUnit = MultipleUnit ["MB", "GB", "TB", "PB"]
                    }
                  , NumberFI
                    { nfiDescriptor = FIDescriptor
                      { iLabel = Just "Total volume of backups"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = []
                      , iMandatory = True
                      }
                    , nfiUnit = MultipleUnit ["MB", "GB", "TB", "PB"]
                    }
                  ]
      }
    providers :: FormItem
    providers = SimpleGroup
      { sgDescriptor = FIDescriptor
        { iLabel = Just "Storage providers"
        , iShortDescription = Nothing
        , iNumbering = NoNumbering
        , iIdent = Nothing
        , iTags = []
        , iLongDescription = Nothing
        , iLink = Nothing
        , iRules = []
        , iMandatory = True
        }
      , sgLevel = 0
      , sgItems = [ NumberFI
                    { nfiDescriptor = FIDescriptor
                      { iLabel = Just "Group's local"
                      , iNumbering = NoNumbering
                      , iIdent = Just "storage-provider-group"
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = [storageSumRule, NumValueRule (\n -> n >= 0 && n <= 100)]
                      , iMandatory = True
                      }
                    , nfiUnit = SingleUnit "%"
                    }
                  , NumberFI
                    { nfiDescriptor = FIDescriptor
                      { iLabel = Just "Institutional"
                      , iNumbering = NoNumbering
                      , iIdent = Just "storage-provider-institutional"
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = [storageSumRule, NumValueRule (\n -> n >= 0 && n <= 100)]
                      , iMandatory = True
                      }
                    , nfiUnit = SingleUnit "%"
                    }
                  , NumberFI
                    { nfiDescriptor = FIDescriptor
                      { iLabel = Just "External Provider"
                      , iNumbering = NoNumbering
                      , iIdent = Just "storage-provider-external"
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = [storageSumRule, NumValueRule (\n -> n >= 0 && n <= 100)]
                      , iMandatory = True
                      }
                    , nfiUnit = SingleUnit "%"
                    }
                  , NumberFI
                    { nfiDescriptor = FIDescriptor
                      { iLabel = Just "Sum"
                      , iNumbering = NoNumbering
                      , iIdent = Just "storage-providers-sum"
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
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