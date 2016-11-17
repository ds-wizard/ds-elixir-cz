#!/bin/bash

rsync -rvz --delete -e ssh bin static rob@ccmi.fit.cvut.cz:~/rsync/elixir-cz.fairdata.solutions
rsync -rvz --delete -e ssh dist/build/Elixir-cz.fairdata.solutions/Elixir-cz.fairdata.solutions rob@ccmi.fit.cvut.cz:~/rsync/elixir-cz.fairdata.solutions/build/Elixir-cz.fairdata.solutions
