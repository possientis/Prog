EXT=gif  # should be gif

for file in *.$EXT; do

  # if there are no files, $file = *.gif and does not exists
  if [ ! -f "$file" ]; then
    exit 0
  fi

  b=$(basename $file .$EXT)

  echo Converting $b.$EXT to $b.png...
  giftopnm $b.$EXT | pnmtopng > $b.png

done
