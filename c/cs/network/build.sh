#!/bin/bash

gcc -o client echoclient.c rio.c connect.c
gcc -o server select.c rio.c connect.c
