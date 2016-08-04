#!/bin/sh
BITCOINJ_JARS=

BITCOINJ_DIR=`dirname $0`

for d in $BITCOINJ_DIR/*.jar
do
  BITCOINJ_JARS="$d:$BITCOINJ_JARS"
done

rm wallet -rf  # clean build

javac -cp "$BITCOINJ_JARS" -d . \
  Main.java \
  NotificationBarPane.java \
  GuiUtils.java \
  TextFieldValidator.java \
  EasingMode.java \
  ElasticInterpolator.java \
  EasingInterpolator.java
  


