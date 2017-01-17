FILENAME=$1

if [ -f "$FILENAME" ]; then # note the space after semicolon
  echo "File $FILENAME exists."; cp $FILENAME $FILENAME.bak
else
  echo "File $FILENAME not found."; touch $FILENAME
fi; echo "File test complete"
