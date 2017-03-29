{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Chapter7 (ch7Roles) where
#ifndef __HASTE__
--import           Data.Text (pack)
#endif
import           FormEngine.FormItem
import           FormStructure.Common

ch7Roles :: FormItem
ch7Roles = Chapter
  { chDescriptor = defaultFIDescriptor { iLabel = Just "7.Roles " }
  , chItems = [roles, remark]
  }
  where
    roles :: FormItem
    roles = SimpleGroup
      { sgDescriptor = defaultFIDescriptor
        { iLabel = Just "Employed roles"
        , iMandatory = True
        }
      , sgLevel = 0
      , sgItems = [ NumberFI
                    { nfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Data producer"
                      , iTags = [Tag "box_1"]
                      , iLink = Just "Haste['toRoles']()"
                      }
                    , nfiUnit = SingleUnit "Full-time equivalent"
                    }
                  , NumberFI
                    { nfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Data expert"
                      , iTags = fmap Tag ["box_2", "box_3", "box_4_1"]
                      , iLink = Just "Haste['toRoles']()"
                      }
                    , nfiUnit = SingleUnit "Full-time equivalent"
                    }
                  , NumberFI
                    { nfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Data consumer"
                      , iTags = [Tag "box_3"]
                      , iLink = Just "Haste['toRoles']()"
                      }
                    , nfiUnit = SingleUnit "Full-time equivalent"
                    }
                  , NumberFI
                    { nfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Data curator"
                      , iTags = fmap Tag ["box_2", "box_3", "box_4_1", "box_5_i", "box_5_e", "box_6"]
                      , iLink = Just "Haste['toRoles']()"
                      }
                    , nfiUnit = SingleUnit "Full-time equivalent"
                    }
                  , NumberFI
                    { nfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Data custodian"
                      , iTags = fmap Tag ["box_4_1", "box_5_i", "box_5_e"]
                      , iLink = Just "Haste['toRoles']()"
                      }
                    , nfiUnit = SingleUnit "Full-time equivalent"
                    }
                  , NumberFI
                    { nfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Data steward"
                      , iTags = fmap Tag ["box_1", "box_2", "box_3", "box_4_1", "box_5_i", "box_5_e", "box_6"]
                      , iLink = Just "Haste['toRoles']()"
                      }
                    , nfiUnit = SingleUnit "Full-time equivalent"
                    }
                  , NumberFI
                    { nfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Data manager"
                      , iTags = fmap Tag ["box_1", "box_2", "box_4_1", "box_5_i", "box_5_e", "box_6"]
                      , iLink = Just "Haste['toRoles']()"
                      }
                    , nfiUnit = SingleUnit "Full-time equivalent"
                    }
                  ]
      }