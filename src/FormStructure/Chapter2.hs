{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Chapter2 (ch2DataProcessing) where
#ifndef __HASTE__
import           Data.Text (pack)
#endif 
import           FormEngine.FormItem
import           FormStructure.Common

ch2DataProcessing :: FormItem
ch2DataProcessing = Chapter
  { chDescriptor = FIDescriptor
    { iNumbering = NoNumbering
    , iLabel = Just "2.Processing "
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
        { iLabel = Just "Do you process raw data, i.e. you produce secondary data?"
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
                                   [ inputVolumes
                                   , outputVolumes
                                   , costProcessing
                                   , management
                                   , accessibility
                                   , remark
                                   ]
                               , SimpleOption "No"
                               ]
      }
      where
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
                          , iIdent = Just "prim-raw-volume"
                          , iTags = [Tag "arrow_1_2"]
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
                          { iLabel = Just "Incoming external specific raw data volume"
                          , iNumbering = NoNumbering
                          , iIdent = Nothing
                          , iTags = [Tag "arrow_L_2"]
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
                          , iIdent = Just "prim-volume"
                          , iTags = [Tag "arrow_2_3", Tag "arrow_2_4"]
                          , iShortDescription = Just "Resulting data from this stage"
                          , iLongDescription = Nothing
                          , iLink = Nothing
                          , iRules = [CopyValueRule "prim-volume" "sec-input-volume", totalSum]
                          , iMandatory = True
                          }
                        , nfiUnit = MultipleUnit ["MB", "GB", "TB", "PB"]
                        }
                      ]
          }
        costProcessing :: FormItem
        costProcessing = SimpleGroup
          { sgDescriptor = FIDescriptor
            { iLabel = Just "Cost of data processing"
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
                  , iIdent = Just "prim-internal-funding-institutional"
                  , iTags = []
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [fundingSumRule, IntValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "National"
                  , iNumbering = NoNumbering
                  , iIdent = Just "prim-internal-funding-national"
                  , iTags = []
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [fundingSumRule, IntValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "European"
                  , iNumbering = NoNumbering
                  , iIdent = Just "prim-internal-funding-european"
                  , iTags = []
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [fundingSumRule, IntValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "World-wide"
                  , iNumbering = NoNumbering
                  , iIdent = Just "prim-internal-funding-worldwide"
                  , iTags = []
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [fundingSumRule, IntValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "Sum"
                  , iNumbering = NoNumbering
                  , iIdent = Just "prim-internal-funding-sum"
                  , iTags = []
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [ReadOnlyRule, IntValueRule (== 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              ]
  }
  where
    fundingSumRule = SumRule
                       [ "prim-internal-funding-institutional"
                       , "prim-internal-funding-national"
                       , "prim-internal-funding-european"
                       , "prim-internal-funding-worldwide"
                       ]
                       "prim-internal-funding-sum"

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
                  , iIdent = Just "prim-external-internal-funding-institutional"
                  , iTags = []
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [fundingSumRule, IntValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "National"
                  , iNumbering = NoNumbering
                  , iIdent = Just "prim-external-internal-funding-national"
                  , iTags = []
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [fundingSumRule, IntValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "European"
                  , iNumbering = NoNumbering
                  , iIdent = Just "prim-external-internal-funding-european"
                  , iTags = []
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [fundingSumRule, IntValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "World-wide"
                  , iNumbering = NoNumbering
                  , iIdent = Just "prim-external-internal-funding-worldwide"
                  , iTags = []
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [fundingSumRule, IntValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "Sum"
                  , iNumbering = NoNumbering
                  , iIdent = Just "prim-external-internal-funding-sum"
                  , iTags = []
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [ReadOnlyRule, IntValueRule (== 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              ]
  }
  where
    fundingSumRule = SumRule
                       [ "prim-external-internal-funding-institutional"
                       , "prim-external-internal-funding-national"
                       , "prim-external-internal-funding-european"
                       , "prim-external-internal-funding-worldwide"
                       ]
                       "prim-external-internal-funding-sum"

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
                  , iIdent = Just "prim-accessibility-inside"
                  , iTags = [Tag "box_5_i"]
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [accSumRule, IntValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "External closed access"
                  , iNumbering = NoNumbering
                  , iIdent = Just "prim-accessibility-closed"
                  , iTags = [Tag "box_5_e", Tag "arrow_5_ca"]
                  , iShortDescription = Just "E.g. based on contract"
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [accSumRule, IntValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "External open access"
                  , iNumbering = NoNumbering
                  , iIdent = Just "prim-accessibility-open"
                  , iTags = [Tag "box_5_e", Tag "arrow_5_oa"]
                  , iShortDescription = Just "Free or paid"
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [accSumRule, IntValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = FIDescriptor
                  { iLabel = Just "Sum"
                  , iNumbering = NoNumbering
                  , iIdent = Just "prim-accessibility-sum"
                  , iTags = []
                  , iShortDescription = Nothing
                  , iLongDescription = Nothing
                  , iLink = Nothing
                  , iRules = [ReadOnlyRule, IntValueRule (== 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              ]
  }
  where
    accSumRule = SumRule
                   [ "prim-accessibility-inside"
                   , "prim-accessibility-closed"
                   , "prim-accessibility-open"
                   ]
                   "prim-accessibility-sum"