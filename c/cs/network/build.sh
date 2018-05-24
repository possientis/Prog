#!/bin/bash

gcc -o client echoclient.c rio.c connect.c
gcc -o server echoserver.c rio.c connect.c
