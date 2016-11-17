module Modes (Mode(..)) where

import Model.Respondent

data Mode = ReadOnly
          | WrongRespondent
          | Filling Respondent
          | Submitted