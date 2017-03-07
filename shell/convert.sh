#!/bin/bash
# convert.sh:

# Converts all the MacPaint image files in a directory to "pbm" format.

#  Uses the "macptopbm" binary from the "netpbm" package,
#+ which is maintained by Brian Henderson (bryanh@giraffe-data.com).
#  Netpbm is a standard part of most Linux distros.


OPERATION=macptopbm
SUFFIX=pbm            # New filename suffix.

if [ -n "$1" ]
then
  directory=$1        # If directory name given as a script argument...
else
  directory=$PWD      # Otherwise use current working directory.
fi


# Assumes all files in the target directory are MacPaint image files,
#+ with a ".mac" filename suffix.

for file in $directory/*.mac  #  filename globbing
do
  filename=${file%.*c}        #  strip ".mac" suffix off filename
                              #+ ('.*c' matches everything
                              #+ between '.' and 'c' inclusive
  $OPERATION $file > "$filename.$SUFFIX"
                              #  redirect conversion to new filename

  rm -f $file                 # delete original file after converting
  echo "$filename.$SUFFIX"    # log what is happening to stdout
done

exit 0


