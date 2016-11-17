{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Chapter6 (ch6DataManagement) where
#ifndef __HASTE__
import           Data.Text (pack)
#endif 
import           FormEngine.FormItem
import           FormStructure.Common

ch6DataManagement :: FormItem
ch6DataManagement = Chapter
  { chDescriptor = FIDescriptor
    { iNumbering = NoNumbering
    , iLabel = Just "6.Management "
    , iIdent = Nothing
    , iTags = []
    , iShortDescription = Nothing
    , iLongDescription = Nothing
    , iLink = Nothing
    , iRules = []
    , iMandatory = False
    }
  , chItems = [for, management, cost6, remark]
  }
  where
    for :: FormItem
    for = SimpleGroup
      { sgDescriptor = FIDescriptor
        { iLabel = Just "We perform data management for:"
        , iNumbering = NoNumbering
        , iIdent = Nothing
        , iTags = []
        , iShortDescription = Nothing
        , iLongDescription = Nothing
        , iLink = Nothing
        , iRules = []
        , iMandatory = False
        }
      , sgLevel = 0
      , sgItems = [ OptionalGroup
                    { ogDescriptor = FIDescriptor
                      { iLabel = Just "local use"
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
                    , ogItems = []
                    }
                  , OptionalGroup
                    { ogDescriptor = FIDescriptor
                      { iLabel = Just "community use"
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
                    , ogItems = []
                    }
                  ]
      }
    management :: FormItem
    management = SimpleGroup
      { sgDescriptor = FIDescriptor
        { iLabel = Just "Management details"
        , iNumbering = NoNumbering
        , iIdent = Nothing
        , iTags = []
        , iShortDescription = Nothing
        , iLongDescription = Nothing
        , iLink = Nothing
        , iRules = []
        , iMandatory = False
        }
      , sgLevel = 0
      , sgItems = [ ChoiceFI
                    { chfiDescriptor = FIDescriptor
                      { iLabel = Just "Do you handle error reports?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = []
                      , iMandatory = False
                      }
                    , chfiAvailableOptions = [SimpleOption "no", SimpleOption "yes"]
                    }
                  , ChoiceFI
                    { chfiDescriptor = FIDescriptor
                      { iLabel = Just "Do you manage versioning?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = []
                      , iMandatory = False
                      }
                    , chfiAvailableOptions = [SimpleOption "no", SimpleOption "yes"]
                    }
                  , ChoiceFI
                    { chfiDescriptor = FIDescriptor
                      { iLabel = Just "Is data actuality maintained (updates)?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = []
                      , iMandatory = False
                      }
                    , chfiAvailableOptions = [SimpleOption "no", SimpleOption "yes"]
                    }
                  , ChoiceFI
                    { chfiDescriptor = FIDescriptor
                      { iLabel = Just "Sustainability"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = []
                      , iMandatory = False
                      }
                    , chfiAvailableOptions = [ SimpleOption "long-term, continuous funding"
                                             , DetailedOption NoNumbering "short-term"
                                                 [ SimpleGroup
                                                   { sgDescriptor = FIDescriptor
                                                     { iLabel = Nothing
                                                     , iNumbering = NoNumbering
                                                     , iIdent = Nothing
                                                     , iTags = []
                                                     , iShortDescription = Nothing
                                                     , iLongDescription = Nothing
                                                     , iLink = Nothing
                                                     , iRules = []
                                                     , iMandatory = False
                                                     }
                                                   , sgLevel = 0
                                                   , sgItems = [ NumberFI
                                                                 { nfiDescriptor = FIDescriptor
                                                                   { iLabel = Just "How long"
                                                                   , iNumbering = NoNumbering
                                                                   , iIdent = Nothing
                                                                   , iTags = []
                                                                   , iShortDescription = Nothing
                                                                   , iLongDescription = Nothing
                                                                   , iLink = Nothing
                                                                   , iRules = []
                                                                   , iMandatory = False
                                                                   }
                                                                 , nfiUnit = SingleUnit "years"
                                                                 }
                                                               ]
                                                   }
                                                 ]
                                             ]
                    }
                  , NumberFI
                    { nfiDescriptor = FIDescriptor
                      { iLabel = Just "Longest required sustainability"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = []
                      , iMandatory = False
                      }
                    , nfiUnit = SingleUnit "years"
                    }
                  , ChoiceFI
                    { chfiDescriptor = FIDescriptor
                      { iLabel = Just "Do you apply some form of data stewardship?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = []
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
      { sgDescriptor = FIDescriptor
        { iLabel = Just "Total cost of data management"
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
                  ]
      }