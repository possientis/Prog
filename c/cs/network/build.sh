#!/bin/bash

gcc -o client echoclient.c rio.c connect.c
gcc -o server -lpthread echoservert.c rio.c connect.c
