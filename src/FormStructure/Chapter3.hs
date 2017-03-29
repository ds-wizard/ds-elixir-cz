{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Chapter3 (ch3DataUsage) where
#ifndef __HASTE__
--import           Data.Text (pack)
#endif
import           FormEngine.FormItem
import           FormStructure.Common

ch3DataUsage :: FormItem
ch3DataUsage = Chapter
  { chDescriptor = defaultFIDescriptor { iLabel = Just "3.Usage " }
  , chItems = [ch2DataProductionQuestion]
  }
  where
    ch2DataProductionQuestion :: FormItem
    ch2DataProductionQuestion = ChoiceFI
      { chfiDescriptor = defaultFIDescriptor
        { iLabel = Just "Do you use data, i.e. to perform analyses?"
        , iMandatory = True
        }
      , chfiAvailableOptions = [ DetailedOption NoNumbering "Yes"
                                   [ usageType
                                   , inputVolumes
                                   , outputVolumes
                                   , cost3
                                   , management
                                   , accessibility
                                   , remark
                                   ]
                               , SimpleOption "No"
                               ]
      }
      where
        usageType :: FormItem
        usageType = SimpleGroup
          { sgDescriptor = defaultFIDescriptor
            { iMandatory = True
            }
          , sgLevel = 0
          , sgItems = [ TextFI
                        { tfiDescriptor = defaultFIDescriptor
                          { iLabel = Just "Describe the usage"
                          , iLongDescription = Just
                                                 "A typical usage is performing a certain analysis."
                          }
                        }
                      ]
          }
        inputVolumes :: FormItem
        inputVolumes = SimpleGroup
          { sgDescriptor = defaultFIDescriptor
            { iLabel = Just "Input data (for 2015)"
            , iMandatory = True
            }
          , sgLevel = 0
          , sgItems = [ NumberFI
                        { nfiDescriptor = defaultFIDescriptor
                          { iLabel = Just "Inhouse produced data volume"
                          , iIdent = Just "sec-input-volume"
                          , iTags = [Tag "arrow_2_3"]
                          , iRules = [ReadOnlyRule]
                          }
                        , nfiUnit = SingleUnit "TB"
                        }
                      , NumberFI
                        { nfiDescriptor = defaultFIDescriptor
                          { iLabel = Just "Incoming external specific primary data volume"
                          , iTags = [Tag "arrow_L_3"]
                          , iShortDescription = Just
                                                  "External data that are not publicly available and are produced specifically for your needs."
                          , iMandatory = True
                          }
                        , nfiUnit = MultipleUnit ["MB", "GB", "TB", "PB"]
                        }
                      , SimpleGroup
                        { sgDescriptor = defaultFIDescriptor
                          { iLabel = Just "Cost of external data purchases"
                          , iMandatory = True
                          }
                        , sgLevel = 0
                        , sgItems = [ NumberFI
                                      { nfiDescriptor = defaultFIDescriptor
                                        { iLabel = Just "For year 2015"
                                        }
                                      , nfiUnit = SingleUnit "thousand EUR"
                                      }
                                    , financingExternal
                                    ]
                        }
                      ]
          }
        outputVolumes :: FormItem
        outputVolumes = SimpleGroup
          { sgDescriptor = defaultFIDescriptor
            { iLabel = Just "Output data volumes (for 2015)"
            , iMandatory = True
            }
          , sgLevel = 0
          , sgItems = [ NumberFI
                        { nfiDescriptor = defaultFIDescriptor
                          { iLabel = Just "Resulting data volume"
                          , iIdent = Just "sec-volume"
                          , iTags = [Tag "arrow_3_4"]
                          , iShortDescription = Just "Resulting data from this stage"
                          , iRules = [totalSum]
                          , iMandatory = True
                          }
                        , nfiUnit = MultipleUnit ["MB", "GB", "TB", "PB"]
                        }
                      ]
          }
        cost3 :: FormItem
        cost3 = SimpleGroup
          { sgDescriptor = defaultFIDescriptor
            { iLabel = Just "Cost of secondary data production"
            , iShortDescription = Just "Rough estimation of FTEs + investments + consumables"
            , iMandatory = True
            }
          , sgLevel = 0
          , sgItems = [ NumberFI
                        { nfiDescriptor = defaultFIDescriptor
                          { iLabel = Just "For year 2015"
                          }
                        , nfiUnit = SingleUnit "thousand EUR"
                        }
                      , financingInternal
                      ]
          }
        management = SimpleGroup
          { sgDescriptor = defaultFIDescriptor
            { iLabel = Just "Maintenance and data sustainability"
            , iShortDescription = Just
                                    "Data represent a valuable asset that should be persisted as long as possible. How is your situation?"
            , iMandatory = True
            }
          , sgLevel = 0
          , sgItems = [ ChoiceFI
                        { chfiDescriptor = defaultFIDescriptor
                          { iLabel = Just "Is the data sustainability plan defined?"
                          , iMandatory = True
                          }
                        , chfiAvailableOptions = [SimpleOption "Yes", SimpleOption "No"]
                        }
                      , ChoiceFI
                        { chfiDescriptor = defaultFIDescriptor
                          { iLabel = Just "How long are the data stored?"
                          , iShortDescription = Just "Longest considered period"
                          , iMandatory = True
                          }
                        , chfiAvailableOptions = [ SimpleOption "weeks"
                                                 , SimpleOption "months"
                                                 , SimpleOption "years"
                                                 , SimpleOption "not limited"
                                                 ]
                        }
                      ]
          }

financingInternal :: FormItem
financingInternal = SimpleGroup
  { sgDescriptor = defaultFIDescriptor
    { iLabel = Just "Funding"
    , iMandatory = True
    }
  , sgLevel = 0
  , sgItems = [ NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "Institutional"
                  , iIdent = Just "sec-internal-funding-institutional"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "National"
                  , iIdent = Just "sec-internal-funding-national"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "European"
                  , iIdent = Just "sec-internal-funding-european"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "World-wide"
                  , iIdent = Just "sec-internal-funding-worldwide"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "Sum"
                  , iIdent = Just "sec-internal-funding-sum"
                  , iRules = [ReadOnlyRule, NumValueRule (== 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              ]
  }
  where
    fundingSumRule = SumRule
                       [ "sec-internal-funding-institutional"
                       , "sec-internal-funding-national"
                       , "sec-internal-funding-european"
                       , "sec-internal-funding-worldwide"
                       ]
                       "sec-internal-funding-sum"

financingExternal :: FormItem
financingExternal = SimpleGroup
  { sgDescriptor = defaultFIDescriptor
    { iLabel = Just "Funding"
    , iMandatory = True
    }
  , sgLevel = 0
  , sgItems = [ NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "Institutional"
                  , iIdent = Just "sec-external-internal-funding-institutional"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "National"
                  , iIdent = Just "sec-external-internal-funding-national"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "European"
                  , iIdent = Just "sec-external-internal-funding-european"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "World-wide"
                  , iIdent = Just "sec-external-internal-funding-worldwide"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >=0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "Sum"
                  , iIdent = Just "sec-external-internal-funding-sum"
                  , iRules = [ReadOnlyRule, NumValueRule (== 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              ]
  }
  where
    fundingSumRule = SumRule
                       [ "sec-external-internal-funding-institutional"
                       , "sec-external-internal-funding-national"
                       , "sec-external-internal-funding-european"
                       , "sec-external-internal-funding-worldwide"
                       ]
                       "sec-external-internal-funding-sum"

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
                  , iIdent = Just "sec-accessibility-inside"
                  , iTags = [Tag "box_5_i"]
                  , iRules = [accSumRule, NumValueRule (<= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "External closed access"
                  , iIdent = Just "sec-accessibility-closed"
                  , iTags = [Tag "box_5_e", Tag "arrow_5_ca"]
                  , iShortDescription = Just "E.g. based on contract"
                  , iRules = [accSumRule, NumValueRule (<= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "External open access"
                  , iIdent = Just "sec-accessibility-open"
                  , iTags = [Tag "box_5_e", Tag "arrow_5_oa"]
                  , iShortDescription = Just "Free or paid"
                  , iRules = [accSumRule, NumValueRule (<= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "Sum"
                  , iIdent = Just "sec-accessibility-sum"
                  , iRules = [ReadOnlyRule, NumValueRule (== 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              ]
  }
  where
    accSumRule = SumRule ["sec-accessibility-inside", "sec-accessibility-closed", "sec-accessibility-open"]
                   "sec-accessibility-sum"