{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Chapter3 (ch3DataUsage) where
#ifndef __HASTE__
--import           Data.Text (pack)
#endif
import           FormEngine.FormItem
import           FormStructure.Common

ch3DataUsage :: FormItem
ch3DataUsage = Chapter
  { chDescriptor = FIDescriptor
    { iNumbering = NoNumbering
    , iLabel = Just "3.Usage "
    , iIdent = Nothing
    , iTags = []
    , iShortDescription = Nothing
    , iLongDescription = Nothing
    , iLink = Nothing
    , iRules = []
    , iMandatory = False
    }
  , chItems = [ch2DataProductionQuestion]
  }
  where
    ch2DataProductionQuestion :: FormItem
    ch2DataProductionQuestion = ChoiceFI
      { chfiDescriptor = FIDescriptor
        { iLabel = Just "Do you use data, i.e. to perform analyses?"
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
          { sgDescriptor = FIDescriptor
            { iLabel = Nothing
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
          , sgItems = [ TextFI
                        { tfiDescriptor = FIDescriptor
                          { iLabel = Just "Describe the usage"
                          , iNumbering = NoNumbering
                          , iIdent = Nothing
                          , iTags = []
                          , iShortDescription = Nothing
                          , iLongDescription = Just
                                                 "A typical usage is performing a certain analysis."
                          , iLink = Nothing
                          , iRules = []
                          , iMandatory = False
                          }
                        }
                      ]
          }
        inputVolumes :: FormItem
        inputVolumes = SimpleGroup
          { sgDescriptor = FIDescriptor
            { iLabel = Just "Input data (for 2015)"
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
          , sgItems = [ NumberFI
                        { nfiDescriptor = FIDescriptor
                          { iLabel = Just "Inhouse produced data volume"
                          , iNumbering = NoNumbering
                          , iIdent = Just "sec-input-volume"
                          , iTags = [Tag "arrow_2_3"]
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
                          { iLabel = Just "Incoming external specific primary data volume"
                          , iNumbering = NoNumbering
                          , iIdent = Nothing
                          , iTags = [Tag "arrow_L_3"]
                          , iShortDescription = Just
                                                  "External data that are not publicly available and are produced specifically for your needs."
                          , iLongDescription = Nothing
                          , iLink = Nothing
                          , iRules = []
                          , iMandatory = True
                          }
                        , nfiUnit = MultipleUnit ["MB", "GB", "TB", "PB"]
                        }
                      , SimpleGroup
                        { sgDescriptor = FIDescriptor
                          { iLabel = Just "Cost of external data purchases"
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
                                        { iLabel = Just "For year 2015"
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
                                    , financingExternal
                                    ]
                        }
                      ]
          }
        outputVolumes :: FormItem
        outputVolumes = SimpleGroup
          { sgDescriptor = FIDescriptor
            { iLabel = Just "Output data volumes (for 2015)"
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
          , sgItems = [ NumberFI
                        { nfiDescriptor = FIDescriptor
                          { iLabel = Just "Resulting data volume"
                          , iNumbering = NoNumbering
                          , iIdent = Just "sec-volume"
                          , iTags = [Tag "arrow_3_4"]
                          , iShortDescription = Just "Resulting data from this stage"
                          , iLongDescription = Nothing
                          , iLink = Nothing
                          , iRules = [totalSum]
                          , iMandatory = True
                          }
                        , nfiUnit = MultipleUnit ["MB", "GB", "TB", "PB"]
                        }
                      ]
          }
        cost3 :: FormItem
        cost3 = SimpleGroup
          { sgDescriptor = FIDescriptor
            { iLabel = Just "Cost of secondary data production"
            , iShortDescription = Just "Rough estimation of FTEs + investments + consumables"
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
                          { iLabel = Just "For year 2015"
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
                      , financingInternal
                      ]
          }
        management = SimpleGroup
          { sgDescriptor = FIDescriptor
            { iLabel = Just "Maintenance and data sustainability"
            , iNumbering = NoNumbering
            , iIdent = Nothing
            , iTags = []
            , iShortDescription = Just
                                    "Data represent a valuable asset that should be persisted as long as possible. How is your situation?"
            , iLongDescription = Nothing
            , iLink = Nothing
            , iRules = []
            , iMandatory = True
            }
          , sgLevel = 0
          , sgItems = [ ChoiceFI
                        { chfiDescriptor = FIDescriptor
                          { iLabel = Just "Is the data sustainability plan defined?"
                          , iNumbering = NoNumbering
                          , iIdent = Nothing
                          , iTags = []
                          , iShortDescription = Nothing
                          , iLongDescription = Nothing
                          , iLink = Nothing
                          , iRules = []
                          , iMandatory = True
                          }
                        , chfiAvailableOptions = [SimpleOption "Yes", SimpleOption "No"]
                        }
                      , ChoiceFI
                        { chfiDescriptor = FIDescriptor
                          { iLabel = Just "How long are the data stored?"
                          , iNumbering = NoNumbering
                          , iIdent = Nothing
                          , iTags = []
                          , iShortDescription = Just "Longest considered period"
                          , iLongDescription = Nothing
                          , iLink = Nothing
                          , iRules = []
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
  { sgDescriptor = FIDescriptor
    { iLabel = Just "Funding"
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
                  { iLabel = Just "Institutional"
                  , iNumbering = NoNumbering
                  , iIdent = Just "sec-internal-funding-institutional"
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
                  , iIdent = Just "sec-internal-funding-national"
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
                  , iIdent = Just "sec-internal-funding-european"
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
                  , iIdent = Just "sec-internal-funding-worldwide"
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
                  , iIdent = Just "sec-internal-funding-sum"
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
                       [ "sec-internal-funding-institutional"
                       , "sec-internal-funding-national"
                       , "sec-internal-funding-european"
                       , "sec-internal-funding-worldwide"
                       ]
                       "sec-internal-funding-sum"

financingExternal :: FormItem
financingExternal = SimpleGroup
  { sgDescriptor = FIDescriptor
    { iLabel = Just "Funding"
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
                  { iLabel = Just "Institutional"
                  , iNumbering = NoNumbering
                  , iIdent = Just "sec-external-internal-funding-institutional"
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
                  , iIdent = Just "sec-external-internal-funding-national"
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
                  , iIdent = Just "sec-external-internal-funding-european"
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
                  , iIdent = Just "sec-external-internal-funding-worldwide"
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
                  , iIdent = Just "sec-external-internal-funding-sum"
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
                       [ "sec-external-internal-funding-institutional"
                       , "sec-external-internal-funding-national"
                       , "sec-external-internal-funding-european"
                       , "sec-external-internal-funding-worldwide"
                       ]
                       "sec-external-internal-funding-sum"

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
                  , iIdent = Just "sec-accessibility-inside"
                  , iTags = [Tag "box_5_i"]
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [accSumRule, NumValueRule (<= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "External closed access"
                  , iNumbering = NoNumbering
                  , iIdent = Just "sec-accessibility-closed"
                  , iTags = [Tag "box_5_e", Tag "arrow_5_ca"]
                  , iShortDescription = Just "E.g. based on contract"
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [accSumRule, NumValueRule (<= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "External open access"
                  , iNumbering = NoNumbering
                  , iIdent = Just "sec-accessibility-open"
                  , iTags = [Tag "box_5_e", Tag "arrow_5_oa"]
                  , iShortDescription = Just "Free or paid"
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [accSumRule, NumValueRule (<= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "Sum"
                  , iNumbering = NoNumbering
                  , iIdent = Just "sec-accessibility-sum"
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
    accSumRule = SumRule ["sec-accessibility-inside", "sec-accessibility-closed", "sec-accessibility-open"]
                   "sec-accessibility-sum"