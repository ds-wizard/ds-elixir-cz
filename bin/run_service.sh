#!/bin/bash

killall Elixir-cz.fairdata.solution
cd /srv/ghc/elixir-cz.fairdata.solution
nohup dist/build/Elixir-cz.fairdata.solution/Elixir-cz.fairdata.solution > run.log &
