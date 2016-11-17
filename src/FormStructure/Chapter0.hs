{-# LANGUAGE OverloadedStrings, CPP #-}

module FormStructure.Chapter0 (ch0GeneralInformation) where
#ifndef __HASTE__
import           Data.Text (pack)
#endif 
import           FormEngine.FormItem
import           FormStructure.Common
import qualified Countries

ch0GeneralInformation :: FormItem
ch0GeneralInformation = Chapter
  { chDescriptor = FIDescriptor
    { iNumbering = NoNumbering
    , iLabel = Just "0.General Info"
    , iIdent = Nothing
    , iTags = []
    , iShortDescription = Nothing
    , iLongDescription = Nothing
    , iLink = Nothing
    , iRules = []
    , iMandatory = False
    }
  , chItems = [identification, institution, remark]
  }
  where
    identification = SimpleGroup
      { sgDescriptor = FIDescriptor
        { iLabel = Just "Registration of the responder"
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
      , sgItems = [ StringFI
                    { sfiDescriptor = FIDescriptor
                      { iLabel = Just "First name"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = []
                      , iMandatory = False
                      }
                    }
                  , StringFI
                    { sfiDescriptor = FIDescriptor
                      { iLabel = Just "Surname"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = []
                      , iMandatory = True
                      }
                    }
                  , EmailFI
                    { efiDescriptor = FIDescriptor
                      { iLabel = Just "Email"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = []
                      , iMandatory = True
                      }
                    }
                  ]
      }
    institution :: FormItem
    institution = SimpleGroup
      { sgDescriptor = FIDescriptor
        { iLabel = Just "Affiliation"
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
      , sgItems = [ ListFI
                    { lfiDescriptor = FIDescriptor
                      { iLabel = Just "Country"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = []
                      , iMandatory = True
                      }
                    , lfiAvailableOptions = Countries.countries
                    }
                  , StringFI
                    { sfiDescriptor = FIDescriptor
                      { iLabel = Just "Institution name"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = []
                      , iMandatory = True
                      }
                    }
                  , StringFI
                    { sfiDescriptor = FIDescriptor
                      { iLabel = Just "Organisation unit"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = []
                      , iMandatory = True
                      }
                    }
                  , ChoiceFI
                    { chfiDescriptor = FIDescriptor
                      { iLabel = Just "Level of unit"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , iLink = Nothing
                      , iRules = []
                      , iMandatory = True
                      }
                    , chfiAvailableOptions = [ SimpleOption "institution"
                                             , SimpleOption "faculty"
                                             , SimpleOption "department"
                                             , SimpleOption "research group"
                                             ]
                    }
                  ]
      }