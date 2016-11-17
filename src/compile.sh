#!/bin/bash

#src/Client/hasteCompile.sh > errors.log

cd ..
cabal build >> src/errors.log
cd src
sed -i -e 's/src\///g ' errors.log
