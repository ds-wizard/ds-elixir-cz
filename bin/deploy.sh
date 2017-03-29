#!/bin/bash

D="~/rsync/elixir-cz.fairdata.solutions"

rsync -rvz --delete -e ssh bin static rob@ccmi.fit.cvut.cz:$D
rsync -rvz --delete -e ssh dist/build/Elixir-cz.fairdata.solutions/Elixir-cz.fairdata.solutions rob@ccmi.fit.cvut.cz:$D/elixir-cz.fairdata.solutions

ssh -t rob@ccmi.fit.cvut.cz "sudo systemctl restart elixir-cz.fairdata.solutions.service"

