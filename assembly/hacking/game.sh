#!/bin/sh

gcc -O2 -o game game_of_chance.c hacking.c
sudo chown root:root game
sudo chmod u+s game
