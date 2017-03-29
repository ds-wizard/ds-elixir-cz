{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Chapter1 (ch1DataProduction) where
#ifndef __HASTE__
--import           Data.Text (pack)
#endif
import           FormEngine.FormItem
import           FormStructure.Common

ch1DataProduction :: FormItem
ch1DataProduction = Chapter
  { chDescriptor = defaultFIDescriptor { iLabel = Just "1.Production " }
  , chItems = [ch1DataProductionQuestion]
  }
  where
    ch1DataProductionQuestion :: FormItem
    ch1DataProductionQuestion = ChoiceFI
      { chfiDescriptor = defaultFIDescriptor
        { iLabel = Just "Do you produce raw data?"
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
          { sgDescriptor = defaultFIDescriptor
            { iLabel = Just "Type of data"
            , iShortDescription = Just "(Estimated) volume of raw data produced inhouse in 2015"
            , iMandatory = True
            }
          , sgLevel = 0
          , sgItems = [ OptionalGroup
                        { ogDescriptor = defaultFIDescriptor
                          { iLabel = Just "Genomics"
                          }
                        , ogLevel = 0
                        , ogItems = [ NumberFI
                                      { nfiDescriptor = defaultFIDescriptor
                                        { iLabel = Just "Volume"
                                        , iIdent = Just "raw-volume-genomics"
                                        , iTags = [Tag "arrow_1_2", Tag "arrow_1_4"]
                                        , iRules = volumeSumRules
                                        , iMandatory = True
                                        }
                                      , nfiUnit = MultipleUnit ["MB", "GB", "TB", "PB"]
                                      }
                                    , NumberFI
                                      { nfiDescriptor = defaultFIDescriptor
                                        { iLabel = Just "Cost for year 2015"
                                        , iIdent = Just "raw-cost-genomics"
                                        , iShortDescription = Just "Rough estimation of FTEs + investments + consumables"
                                        , iRules = [costSumRule]
                                        }
                                      , nfiUnit = SingleUnit "thousand EUR"
                                      }
                                    ]
                        }
                      , OptionalGroup
                        { ogDescriptor = defaultFIDescriptor
                          { iLabel = Just "Proteomics"
                          }
                        , ogLevel = 0
                        , ogItems = [ NumberFI
                                      { nfiDescriptor = defaultFIDescriptor
                                        { iLabel = Just "Volume"
                                        , iIdent = Just "raw-volume-proteomics"
                                        , iTags = [Tag "arrow_1_2", Tag "arrow_1_4"]
                                        , iRules = volumeSumRules
                                        , iMandatory = True
                                        }
                                      , nfiUnit = MultipleUnit ["MB", "GB", "TB", "PB"]
                                      }
                                    , NumberFI
                                      { nfiDescriptor = defaultFIDescriptor
                                        { iLabel = Just "Cost for year 2015"
                                        , iIdent = Just "raw-cost-proteomics"
                                        , iShortDescription = Just "Rough estimation of FTEs + investments + consumables"
                                        , iRules = [costSumRule]
                                        }
                                      , nfiUnit = SingleUnit "thousand EUR"
                                      }
                                    ]
                        }
                      , OptionalGroup
                        { ogDescriptor = defaultFIDescriptor
                          { iLabel = Just "Others"
                          }
                        , ogLevel = 0
                        , ogItems = [ StringFI
                                      { sfiDescriptor = defaultFIDescriptor
                                        { iLabel = Just "Specify the output type of raw data"
                                        , iLongDescription = Just "Images, chips, spectra, ..."
                                        , iMandatory = True
                                        }
                                      }
                                    , NumberFI
                                      { nfiDescriptor = defaultFIDescriptor
                                        { iLabel = Just "Volume"
                                        , iIdent = Just "raw-volume-others"
                                        , iTags = [Tag "arrow_1_2", Tag "arrow_1_4"]
                                        , iRules = volumeSumRules
                                        , iMandatory = True
                                        }
                                      , nfiUnit = MultipleUnit ["MB", "GB", "TB", "PB"]
                                      }
                                    , NumberFI
                                      { nfiDescriptor = defaultFIDescriptor
                                        { iLabel = Just "Cost for year 2015"
                                        , iIdent = Just "raw-cost-others"
                                        , iShortDescription = Just "Rough estimation of FTEs + investments + consumables"
                                        , iRules = [costSumRule]
                                        }
                                      , nfiUnit = SingleUnit "thousand EUR"
                                      }
                                    ]
                        }
                      , NumberFI
                        { nfiDescriptor = defaultFIDescriptor
                          { iLabel = Just "Raw data production volume"
                          , iIdent = Just "raw-volume-sum"
                          , iRules = [ReadOnlyRule, totalSum]
                          }
                        , nfiUnit = SingleUnit "TB"
                        }
                      , NumberFI
                        { nfiDescriptor = defaultFIDescriptor
                          { iLabel = Just "Raw data production cost"
                          , iIdent = Just "raw-cost-sum"
                          , iRules = [ReadOnlyRule]
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
  { sgDescriptor = defaultFIDescriptor
    { iLabel = Just "Funding"
    , iShortDescription = Just "Skip if you do not want to share"
    , iMandatory = True
    }
  , sgLevel = 0
  , sgItems = [ NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "Institutional"
                  , iIdent = Just "raw-funding-institutional"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "National"
                  , iIdent = Just "raw-funding-national"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "European"
                  , iIdent = Just "raw-funding-european"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "World-wide"
                  , iIdent = Just "raw-funding-worldwide"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "Sum"
                  , iIdent = Just "raw-funding-sum"
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
  { sgDescriptor = defaultFIDescriptor
    { iLabel = Just "Accesibility modes of your data:"
    , iMandatory = True
    }
  , sgLevel = 0
  , sgItems = [ NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "Internal inside project / collaboration"
                  , iIdent = Just "raw-accessibility-inside"
                  , iTags = [Tag "box_5_i"]
                  , iRules = [accSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "External closed access"
                  , iIdent = Just "raw-accessibility-closed"
                  , iTags = [Tag "box_5_e", Tag "arrow_5_ca"]
                  , iShortDescription = Just "E.g. based on contract"
                  , iRules = [accSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "External open access"
                  , iIdent = Just "raw-accessibility-open"
                  , iTags = [Tag "box_5_e", Tag "arrow_5_oa"]
                  , iShortDescription = Just "Free or paid"
                  , iRules = [accSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "Sum"
                  , iIdent = Just "raw-accessibility-sum"
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