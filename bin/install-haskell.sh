#!/bin/bash

rm -rf .cabal* cabal.sandbox.config dist
cabal sandbox init
cabal update
cabal install --dependencies-only