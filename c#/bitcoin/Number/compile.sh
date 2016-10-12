#!/bin/sh

rm -f *.exe
rm -f *.netmodule

echo $PKG_CONFIG_PATH

mcs Number.cs Number1.cs NumberFactory.cs NumberFactory1.cs -target:module -out:libNumber /reference:System.Numerics.dll

mcs "$@" -addmodule:libNumber /reference:System.Numerics.dll

