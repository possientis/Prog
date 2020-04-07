#!/bin/bash

echo -n "Coreutils: "; chown --version | head -n1 | cut -d")" -f2
