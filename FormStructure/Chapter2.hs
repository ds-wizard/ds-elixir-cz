{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Chapter2 (ch2DataProcessing) where

#ifndef __HASTE__
--import           Data.Text.Lazy (pack)
#endif

import           FormEngine.FormItem
import           FormStructure.Common

ch2DataProcessing :: FormItem
ch2DataProcessing = Chapter
  { chDescriptor = defaultFIDescriptor { iLabel = Just "2.Processing " }
  , chItems = [ch2DataProductionQuestion]
  }
  where
    ch2DataProductionQuestion :: FormItem
    ch2DataProductionQuestion = ChoiceFI
      { chfiDescriptor = defaultFIDescriptor
        { iLabel = Just "Do you process raw data, i.e. you produce secondary data?"
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
          { sgDescriptor = defaultFIDescriptor
            { iLabel = Just "Input data (for 2016)"
            , iMandatory = True
            }
          , sgLevel = 0
          , sgItems = [ NumberFI
                        { nfiDescriptor = defaultFIDescriptor
                          { iLabel = Just "Inhouse produced data volume"
                          , iIdent = Just "prim-raw-volume"
                          , iTags = [Tag "arrow_1_2"]
                          , iRules = [ReadOnlyRule]
                          }
                        , nfiUnit = SingleUnit "TB"
                        }
                      , NumberFI
                        { nfiDescriptor = defaultFIDescriptor
                          { iLabel = Just "Incoming external specific raw data volume"
                          , iTags = [Tag "arrow_L_2"]
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
                                        { iLabel = Just "For year 2016"
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
            { iLabel = Just "Output data volumes (for 2016)"
            , iMandatory = True
            }
          , sgLevel = 0
          , sgItems = [ NumberFI
                        { nfiDescriptor = defaultFIDescriptor
                          { iLabel = Just "Resulting data volume"
                          , iIdent = Just "prim-volume"
                          , iTags = [Tag "arrow_2_3", Tag "arrow_2_4"]
                          , iShortDescription = Just "Resulting data from this stage"
                          , iRules = [CopyValueRule "prim-volume" "sec-input-volume", totalSum]
                          , iMandatory = True
                          }
                        , nfiUnit = MultipleUnit ["MB", "GB", "TB", "PB"]
                        }
                      ]
          }
        costProcessing :: FormItem
        costProcessing = SimpleGroup
          { sgDescriptor = defaultFIDescriptor
            { iLabel = Just "Cost of data processing"
            , iShortDescription = Just "Rough estimation of FTEs + investments + consumables"
            , iMandatory = True
            }
          , sgLevel = 0
          , sgItems = [ NumberFI
                        { nfiDescriptor = defaultFIDescriptor
                          { iLabel = Just "For year 2016"
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
    , iShortDescription = Just "Relevant just in case cost > 0. Skip if you do not want to share"
    }
  , sgLevel = 0
  , sgItems = [ NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "Institutional"
                  , iIdent = Just "prim-internal-funding-institutional"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "National"
                  , iIdent = Just "prim-internal-funding-national"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "European"
                  , iIdent = Just "prim-internal-funding-european"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "World-wide"
                  , iIdent = Just "prim-internal-funding-worldwide"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "Sum"
                  , iIdent = Just "prim-internal-funding-sum"
                  , iRules = [ReadOnlyRule, NumValueRule (== 100)]
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
  { sgDescriptor = defaultFIDescriptor
    { iLabel = Just "Funding"
    , iMandatory = True
    , iShortDescription = Just "Relevant just in case cost > 0. Skip if you do not want to share"
    }
  , sgLevel = 0
  , sgItems = [ NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "Institutional"
                  , iIdent = Just "prim-external-internal-funding-institutional"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "National"
                  , iIdent = Just "prim-external-internal-funding-national"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "European"
                  , iIdent = Just "prim-external-internal-funding-european"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "World-wide"
                  , iIdent = Just "prim-external-internal-funding-worldwide"
                  , iRules = [fundingSumRule, NumValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "Sum"
                  , iIdent = Just "prim-external-internal-funding-sum"
                  , iRules = [ReadOnlyRule, NumValueRule (== 100)]
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
  { sgDescriptor = defaultFIDescriptor
    { iLabel = Just "Accesibility modes of your data:"
    , iMandatory = True
    }
  , sgLevel = 0
  , sgItems = [ NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "Internal inside project / collaboration"
                  , iIdent = Just "prim-accessibility-inside"
                  , iTags = [Tag "box_5_i"]
                  , iRules = [accSumRule, NumValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "External closed access"
                  , iIdent = Just "prim-accessibility-closed"
                  , iTags = [Tag "box_5_e", Tag "arrow_5_ca"]
                  , iShortDescription = Just "E.g. based on contract"
                  , iRules = [accSumRule, NumValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "External open access"
                  , iIdent = Just "prim-accessibility-open"
                  , iTags = [Tag "box_5_e", Tag "arrow_5_oa"]
                  , iShortDescription = Just "Free or paid"
                  , iRules = [accSumRule, NumValueRule (\n -> n >= 0 && n <= 100)]
                  , iMandatory = True
                  }
                , nfiUnit = SingleUnit "%"
                }
              , NumberFI
                { nfiDescriptor = defaultFIDescriptor
                  { iLabel = Just "Sum"
                  , iIdent = Just "prim-accessibility-sum"
                  , iRules = [ReadOnlyRule, NumValueRule (== 100)]
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