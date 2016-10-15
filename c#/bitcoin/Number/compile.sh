#!/bin/sh

rm -f *.exe
rm -f *.dll

mcs   Number.cs               \
      Number1.cs              \
      Number2.cs              \
      NumberFactory.cs        \
      NumberFactory1.cs       \
      NumberFactory2.cs       \
      -t:library              \
      -o:Number.dll           \
      -r:System.Numerics.dll


mcs "$@"                      \
       Test_Abstract.cs       \
      -r:Number.dll           \
      -r:System.Numerics.dll

