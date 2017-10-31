{-# LANGUAGE OverloadedStrings #-}

module FormStructure.FormStructure (formItems) where

import           FormEngine.FormItem

import           FormStructure.Chapter0
import           FormStructure.Chapter1
import           FormStructure.Chapter2
import           FormStructure.Chapter3
import           FormStructure.Chapter4
import           FormStructure.Chapter5
import           FormStructure.Chapter6
import           FormStructure.Chapter7

formItems :: [FormItem]
formItems = prepareForm
             [
              ch0GeneralInformation
            , ch1DataProduction
            , ch2DataProcessing
            , ch3DataUsage
            , ch4DataStorage
            , ch5DataAccessibility
            , ch6DataManagement
            , ch7Roles
             ]