{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Chapter6 (ch6DataManagement) where
#ifndef __HASTE__
--import           Data.Text (pack)
#endif
import           FormEngine.FormItem
import           FormStructure.Common

ch6DataManagement :: FormItem
ch6DataManagement = Chapter
  { chDescriptor = defaultFIDescriptor { iLabel = Just "6.Management " }
  , chItems = [for, management, cost6, remark]
  }
  where
    for :: FormItem
    for = SimpleGroup
      { sgDescriptor = defaultFIDescriptor
        { iLabel = Just "We perform data management for:"
        }
      , sgLevel = 0
      , sgItems = [ OptionalGroup
                    { ogDescriptor = defaultFIDescriptor
                      { iLabel = Just "local use"
                      }
                    , ogLevel = 0
                    , ogItems = []
                    }
                  , OptionalGroup
                    { ogDescriptor = defaultFIDescriptor
                      { iLabel = Just "community use"
                      }
                    , ogLevel = 0
                    , ogItems = []
                    }
                  ]
      }
    management :: FormItem
    management = SimpleGroup
      { sgDescriptor = defaultFIDescriptor
        { iLabel = Just "Management details"
        }
      , sgLevel = 0
      , sgItems = [ ChoiceFI
                    { chfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Do you handle error reports?"
                      }
                    , chfiAvailableOptions = [SimpleOption "no", SimpleOption "yes"]
                    }
                  , ChoiceFI
                    { chfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Do you manage versioning?"
                      }
                    , chfiAvailableOptions = [SimpleOption "no", SimpleOption "yes"]
                    }
                  , ChoiceFI
                    { chfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Is data actuality maintained (updates)?"
                      }
                    , chfiAvailableOptions = [SimpleOption "no", SimpleOption "yes"]
                    }
                  , ChoiceFI
                    { chfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Sustainability"
                      }
                    , chfiAvailableOptions = [ SimpleOption "long-term, continuous funding"
                                             , DetailedOption NoNumbering "short-term"
                                                 [ SimpleGroup
                                                   { sgDescriptor = defaultFIDescriptor
                                                   , sgLevel = 0
                                                   , sgItems = [ NumberFI
                                                                 { nfiDescriptor = defaultFIDescriptor
                                                                   { iLabel = Just "How long"
                                                                   }
                                                                 , nfiUnit = SingleUnit "years"
                                                                 }
                                                               ]
                                                   }
                                                 ]
                                             ]
                    }
                  , NumberFI
                    { nfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Longest required sustainability"
                      }
                    , nfiUnit = SingleUnit "years"
                    }
                  , ChoiceFI
                    { chfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Do you apply some form of data stewardship?"
                      , iMandatory = True
                      }
                    , chfiAvailableOptions = [ DetailedOption NoNumbering "Yes" [xhow]
                                             , SimpleOption "No"
                                             ]
                    }
                  ]
      }

    cost6 :: FormItem
    cost6 = SimpleGroup
      { sgDescriptor = defaultFIDescriptor
        { iLabel = Just "Total cost of data management"
        , iMandatory = True
        }
      , sgLevel = 0
      , sgItems = [ NumberFI
                    { nfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "For year 2015"
                      }
                    , nfiUnit = SingleUnit "thousand EUR"
                    }
                  ]
      }