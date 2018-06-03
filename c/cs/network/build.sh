#!/bin/bash

gcc -o client echoclient.c rio.c connect.c
gcc -o server echoserverp.c rio.c connect.c
