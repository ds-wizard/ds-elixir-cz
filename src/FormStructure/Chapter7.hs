{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Chapter7 (ch7Roles) where
#ifndef __HASTE__
--import           Data.Text (pack)
#endif
import           FormEngine.FormItem
import           FormStructure.Common

ch7Roles :: FormItem
ch7Roles = Chapter
  { chDescriptor = FIDescriptor
    { iNumbering = NoNumbering
    , iLabel = Just "7.Roles "
    , iIdent = Nothing
    , iTags = []
    , iShortDescription = Nothing
    , iLongDescription = Nothing
    , iLink = Nothing
    , iRules = []
    , iMandatory = False
    }
  , chItems = [roles, remark]
  }
  where
    roles :: FormItem
    roles = SimpleGroup
      { sgDescriptor = FIDescriptor
        { iNumbering = NoNumbering
        , iLabel = Just "Employed roles"
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
                      { iLabel = Just "Data producer"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = [Tag "box_1"]
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Just "Haste['toRoles']()"
                      , iRules = []
                      , iMandatory = False
                      }
                    , nfiUnit = SingleUnit "Full-time equivalent"
                    }
                  , NumberFI
                    { nfiDescriptor = FIDescriptor
                      { iLabel = Just "Data expert"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = fmap Tag ["box_2", "box_3", "box_4_1"]
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Just "Haste['toRoles']()"
                      , iRules = []
                      , iMandatory = False
                      }
                    , nfiUnit = SingleUnit "Full-time equivalent"
                    }
                  , NumberFI
                    { nfiDescriptor = FIDescriptor
                      { iLabel = Just "Data consumer"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = [Tag "box_3"]
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Just "Haste['toRoles']()"
                      , iRules = []
                      , iMandatory = False
                      }
                    , nfiUnit = SingleUnit "Full-time equivalent"
                    }
                  , NumberFI
                    { nfiDescriptor = FIDescriptor
                      { iLabel = Just "Data curator"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = fmap Tag ["box_2", "box_3", "box_4_1", "box_5_i", "box_5_e", "box_6"]
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Just "Haste['toRoles']()"
                      , iRules = []
                      , iMandatory = False
                      }
                    , nfiUnit = SingleUnit "Full-time equivalent"
                    }
                  , NumberFI
                    { nfiDescriptor = FIDescriptor
                      { iLabel = Just "Data custodian"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = fmap Tag ["box_4_1", "box_5_i", "box_5_e"]
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Just "Haste['toRoles']()"
                      , iRules = []
                      , iMandatory = False
                      }
                    , nfiUnit = SingleUnit "Full-time equivalent"
                    }
                  , NumberFI
                    { nfiDescriptor = FIDescriptor
                      { iLabel = Just "Data steward"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = fmap Tag ["box_1", "box_2", "box_3", "box_4_1", "box_5_i", "box_5_e", "box_6"]
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Just "Haste['toRoles']()"
                      , iRules = []
                      , iMandatory = False
                      }
                    , nfiUnit = SingleUnit "Full-time equivalent"
                    }
                  , NumberFI
                    { nfiDescriptor = FIDescriptor
                      { iLabel = Just "Data manager"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = fmap Tag ["box_1", "box_2", "box_4_1", "box_5_i", "box_5_e", "box_6"]
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Just "Haste['toRoles']()"
                      , iRules = []
                      , iMandatory = False
                      }
                    , nfiUnit = SingleUnit "Full-time equivalent"
                    }
                  ]
      }