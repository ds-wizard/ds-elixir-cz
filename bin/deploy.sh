#!/bin/bash

rsync -rvz --delete -e ssh bin static rob@ccmi.fit.cvut.cz:~/rsync/elixir-cz.fairdata.solution
rsync -rvz --delete -e ssh dist/build/Elixir-cz.fairdata.solution/Elixir-cz.fairdata.solution rob@ccmi.fit.cvut.cz:~/rsync/elixir-cz.fairdata.solution/build/Elixir-cz.fairdata.solution
