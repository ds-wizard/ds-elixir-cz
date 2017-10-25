{-# LANGUAGE OverloadedStrings, NamedFieldPuns, CPP #-}

module FormStructure.Chapter0 (ch0GeneralInformation) where

#ifndef __HASTE__
--import           Data.Text.Lazy (Text)
#endif

import           FormEngine.FormItem
import           FormStructure.Common
import qualified FormStructure.Countries as Countries

ch0GeneralInformation :: FormItem
ch0GeneralInformation = Chapter
  { chDescriptor = defaultFIDescriptor { iLabel = Just "0.General Info" }
  , chItems = [identification, institution, remark]
  }
  where
    identification = SimpleGroup
      { sgDescriptor = defaultFIDescriptor
        { iLabel = Just "Registration of the responder"
        , iMandatory = True
        }
      , sgLevel = 0
      , sgItems = [ StringFI
                    { sfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "First name"
                      }
                    }
                  , StringFI
                    { sfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Surname"
                      , iMandatory = True
                      }
                    }
                  , EmailFI
                    { efiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Email"
                      , iMandatory = True
                      }
                    }
                  ]
      }
    institution :: FormItem
    institution = SimpleGroup
      { sgDescriptor = defaultFIDescriptor
        { iLabel = Just "Affiliation"
        , iMandatory = True
        }
      , sgLevel = 0
      , sgItems = [ ListFI
                    { lfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Country"
                      , iMandatory = True
                      }
                    , lfiAvailableOptions = Countries.countries
                    }
                  , StringFI
                    { sfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Institution name"
                      , iMandatory = True
                      }
                    }
                  , StringFI
                    { sfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Organisation unit"
                      , iMandatory = True
                      }
                    }
                  , ChoiceFI
                    { chfiDescriptor = defaultFIDescriptor
                      { iLabel = Just "Level of unit"
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