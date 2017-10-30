#!/bin/bash

F="Elixir-cz-fairdata-solutions"
S="elixir-cz.fairdata.solutions"
D="~/rsync/$S"

ssh -t rob@ccmi.fit.cvut.cz "tar cfzv $S.tar.gz $D"

stack install
rsync -rvz --delete -e ssh bin static rob@ccmi.fit.cvut.cz:$D
ssh -t rob@ccmi.fit.cvut.cz "sudo systemctl stop $S.service"
scp ~/.local/bin/$F rob@ccmi.fit.cvut.cz:$D/$S
ssh -t rob@ccmi.fit.cvut.cz "sudo systemctl start $S.service"
