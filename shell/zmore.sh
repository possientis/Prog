# View gzipped file with 'more' filter

E_NOARGS=85
E_NOTFOUND=86
E_NOTGZIP=87

if [ $# -eq 0 ] # same as: if [ -z "$1" ]
# $1 can exist, but be empty: zmore "" arg1 arg2
then
  echo "Usage: $(basename $0) filename" >&2  # error to stderr
  exit $E_NOARGS
fi

filename=$1

if [ ! -f "$filename" ] # quoting $filename allows for possible spaces
then
  echo "File $filename not found!" >&2      # error to stderr 
  exit $E_NOTFOUND
fi

# testing file extension
if [ ${filename##*.} != "gz" ]  # using bracket in variable subsitution
then
  echo "File $1 is not a gzipped file!"
  exit $E_NOTGZIP
fi

zcat $1 | more

exit $? # returns exit status of pipe
# This is actually unnecessary as the script will, in any case,
# return the exit status of the last command executed
