#!/bin/bash

xdotool search "make run" windowactivate
if [ $? -eq 0 ]; then
    xdotool key ctrl+c
    xdotool type "make run"
    xdotool key KP_Enter
    sleep 0.5
    xdotool search "Questionnaire" windowactivate --sync key --clearmodifiers ctrl+r
fi