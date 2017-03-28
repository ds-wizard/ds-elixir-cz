{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Chapter1 (ch1DataProduction) where
#ifndef __HASTE__
--import           Data.Text (pack)
#endif
import           FormEngine.FormItem
import           FormStructure.Common

ch1DataProduction :: FormItem
ch1DataProduction = Chapter
  { chDescriptor = FIDescriptor
    { iNumbering = NoNumbering
    , iLabel = Just "1.Production "
    , iIdent = Nothing
    , iTags = []
    , iShortDescription = Nothing
    , iLongDescription = Nothing
    , iLink = Nothing
    , iRules = []
    , iMandatory = False
    }
  , chItems = [ch1DataProductionQuestion]
  }
  where
    ch1DataProductionQuestion :: FormItem
    ch1DataProductionQuestion = ChoiceFI
      { chfiDescriptor = FIDescriptor
        { iLabel = Just "Do you produce raw data?"
        , iNumbering = NoNumbering
        , iIdent = Nothing
        , iTags = []
        , iShortDescription = Nothing
        , iLongDescription = Nothing
        , iLink = Nothing
        , iRules = []
        , iMandatory = True
        }
      , chfiAvailableOptions = [ DetailedOption NoNumbering "Yes"
                                   [domains, financing, accessibility, remark]
                               , SimpleOption "No"
                               ]
      }
      where
        domains :: FormItem
        domains = SimpleGroup
          { sgDescriptor = FIDescriptor
            { iLabel = Just "Type of data"
            , iShortDescription = Just "(Estimated) volume of raw data produced inhouse in 2015"
            , iNumbering = NoNumbering
            , iIdent = Nothing
            , iTags = []
            , iLongDescription = Nothing
            , iLink = Nothing
            , iRules = []
            , iMandatory = True
            }
          , sgLevel = 0
          , sgItems = [ OptionalGroup
                        { ogDescriptor = FIDescriptor
                          { iLabel = Just "Genomics"
                          , iNumbering = NoNumbering
                          , iIdent = Nothing
                          , iTags = []
                          , iShortDescription = Nothing
                          , iLongDescription = Nothing
                          , iLink = Nothing
                          , iRules = []
                          , iMandatory = False
                          }
                        , ogLevel = 0
                        , ogItems = [ NumberFI
                                      { nfiDescriptor = FIDescriptor
                                        { iLabel = Just "Volume"
                                        , iNumbering = NoNumbering
                                        , iIdent = Just "raw-volume-genomics"
                                        , iTags = [Tag "arrow_1_2", Tag "arrow_1_4"]
                                        , iShortDescription = Nothing
                                        , iLongDescription = Nothing
                                        , iLink = Nothing
                                        , iRules = volumeSumRules
                                        , iMandatory = True
                                        }
                                      , nfiUnit = MultipleUnit ["MB", "GB", "TB", "PB"]
                                      }
                                    , NumberFI
                                      { nfiDescriptor = FIDescriptor
                                        { iLabel = Just "Cost for year 2015"
                                        , iNumbering = NoNumbering
                                        , iIdent = Just "raw-cost-genomics"
                                        , iTags = []
                                        , iShortDescription = Just "Rough estimation of FTEs + investments + consumables"
                                        , iLongDescription = Nothing
                                        , iLink = Nothing
                                        , iRules = [costSumRule]
                                        , iMandatory = False
                                        }
                                      , nfiUnit = SingleUnit "thousand EUR"
                                      }
                                    ]
                        }
                      , OptionalGroup
                        { ogDescriptor = FIDescriptor
                          { iLabel = Just "Proteomics"
                          , iNumbering = NoNumbering
                          , iIdent = Nothing
                          , iTags = []
                          , iShortDescription = Nothing
                          , iLongDescription = Nothing
                          , iLink = Nothing
                          , iRules = []
                          , iMandatory = False
                          }
                        , ogLevel = 0
                        , ogItems = [ NumberFI
                                      { nfiDescriptor = FIDescriptor
                                        { iLabel = Just "Volume"
                                        , iNumbering = NoNumbering
                                        , iIdent = Just "raw-volume-proteomics"
                                        , iTags = [Tag "arrow_1_2", Tag "arrow_1_4"]
                                        , iShortDescription = Nothing
                                        , iLongDescription = Nothing
                                        , iLink = Nothing
                                        , iRules = volumeSumRules
                                        , iMandatory = True
                                        }
                                      , nfiUnit = MultipleUnit ["MB", "GB", "TB", "PB"]
                                      }
                                    , NumberFI
                                      { nfiDescriptor = FIDescriptor
                                        { iLabel = Just "Cost for year 2015"
                                        , iNumbering = NoNumbering
                                        , iIdent = Just "raw-cost-proteomics"
                                        , iTags = []
                                        , iShortDescription = Just "Rough estimation of FTEs + investments + consumables"
                                        , iLongDescription = Nothing
                                        , iLink = Nothing
                                        , iRules = [costSumRule]
                                        , iMandatory = False
                                        }
                                      , nfiUnit = SingleUnit "thousand EUR"
                                      }
                                    ]
                        }
                      , OptionalGroup
                        { ogDescriptor = FIDescriptor
                          { iLabel = Just "Others"
                          , iNumbering = NoNumbering
                          , iIdent = Nothing
                          , iTags = []
                          , iShortDescription = Nothing
                          , iLongDescription = Nothing
                          , iLink = Nothing
                          , iRules = []
                          , iMandatory = False
                          }
                        , ogLevel = 0
                        , ogItems = [ StringFI
                                      { sfiDescriptor = FIDescriptor
                                        { iLabel = Just "Specify the output type of raw data"
                                        , iNumbering = NoNumbering
                                        , iIdent = Nothing
                                        , iTags = []
                                        , iShortDescription = Nothing
                                        , iLongDescription = Just "Images, chips, spectra, ..."
                                        , iLink = Nothing
                                        , iRules = []
                                        , iMandatory = True
                                        }
                                      }
                                    , NumberFI
                                      { nfiDescriptor = FIDescriptor
                                        { iLabel = Just "Volume"
                                        , iNumbering = NoNumbering
                                        , iIdent = Just "raw-volume-others"
                                        , iTags = [Tag "arrow_1_2", Tag "arrow_1_4"]
                                        , iShortDescription = Nothing
                                        , iLongDescription = Nothing
                                        , iLink = Nothing
                                        , iRules = volumeSumRules
                                        , iMandatory = True
                                        }
                                      , nfiUnit = MultipleUnit ["MB", "GB", "TB", "PB"]
                                      }
                                    , NumberFI
                                      { nfiDescriptor = FIDescriptor
                                        { iLabel = Just "Cost for year 2015"
                                        , iNumbering = NoNumbering
                                        , iIdent = Just "raw-cost-others"
                                        , iTags = []
                                        , iShortDescription = Just "Rough estimation of FTEs + investments + consumables"
                                        , iLongDescription = Nothing
                                        , iLink = Nothing
                                        , iRules = [costSumRule]
                                        , iMandatory = False
                                        }
                                      , nfiUnit = SingleUnit "thousand EUR"
                                      }
                                    ]
                        }
                      , NumberFI
                        { nfiDescriptor = FIDescriptor
                          { iLabel = Just "Raw data production volume"
                          , iNumbering = NoNumbering
                          , iIdent = Just "raw-volume-sum"
                          , iTags = []
                          , iShortDescription = Nothing
                          , iLongDescription = Nothing
                          , iLink = Nothing
                          , iRules = [ReadOnlyRule, totalSum]
                          , iMandatory = False
                          }
                        , nfiUnit = SingleUnit "TB"
                        }
                      , NumberFI
                        { nfiDescriptor = FIDescriptor
                          { iLabel = Just "Raw data production cost"
                          , iNumbering = NoNumbering
                          , iIdent = Just "raw-cost-sum"
                          , iTags = []
                          , iShortDescription = Nothing
                          , iLongDescription = Nothing
                          , iLink = Nothing
                          , iRules = [ReadOnlyRule]
                          , iMandatory = False
                          }
                        , nfiUnit = SingleUnit "thousand EUR"
                        }
                      ]
          }
        volumeSumRules = [ SumTBsRule
                             ["raw-volume-genomics", "raw-volume-proteomics", "raw-volume-others"]
                             "raw-volume-sum"
                         , CopyValueRule "raw-volume-sum" "prim-raw-volume"
                         ]
        costSumRule = SumRule ["raw-cost-genomics", "raw-cost-proteomics", "raw-cost-others"]
                        "raw-cost-sum"

financing :: FormItem
financing = SimpleGroup
  { sgDescriptor = FIDescriptor
    { iLabel = Just "Funding"
    , iShortDescription = Just "Skip if you do not want to share"
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
                  { iLabel = Just "Institutional"
                  , iNumbering = NoNumbering
                  , iIdent = Just "raw-funding-institutional"
                  , iTags = []
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "National"
                  , iNumbering = NoNumbering
                  , iIdent = Just "raw-funding-national"
                  , iTags = []
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "European"
                  , iNumbering = NoNumbering
                  , iIdent = Just "raw-funding-european"
                  , iTags = []
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "World-wide"
                  , iNumbering = NoNumbering
                  , iIdent = Just "raw-funding-worldwide"
                  , iTags = []
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "Sum"
                  , iNumbering = NoNumbering
                  , iIdent = Just "raw-funding-sum"
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
    fundingSumRule = SumRule
                       [ "raw-funding-institutional"
                       , "raw-funding-national"
                       , "raw-funding-european"
                       , "raw-funding-worldwide"
                       ]
                       "raw-funding-sum"

accessibility :: FormItem
accessibility = SimpleGroup
  { sgDescriptor = FIDescriptor
    { iLabel = Just "Accesibility modes of your data:"
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
                  { iLabel = Just "Internal inside project / collaboration"
                  , iNumbering = NoNumbering
                  , iIdent = Just "raw-accessibility-inside"
                  , iTags = [Tag "box_5_i"]
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [accSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "External closed access"
                  , iNumbering = NoNumbering
                  , iIdent = Just "raw-accessibility-closed"
                  , iTags = [Tag "box_5_e", Tag "arrow_5_ca"]
                  , iShortDescription = Just "E.g. based on contract"
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [accSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "External open access"
                  , iNumbering = NoNumbering
                  , iIdent = Just "raw-accessibility-open"
                  , iTags = [Tag "box_5_e", Tag "arrow_5_oa"]
                  , iShortDescription = Just "Free or paid"
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [accSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "Sum"
                  , iNumbering = NoNumbering
                  , iIdent = Just "raw-accessibility-sum"
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
    accSumRule = SumRule ["raw-accessibility-inside", "raw-accessibility-closed", "raw-accessibility-open"]
                   "raw-accessibility-sum"