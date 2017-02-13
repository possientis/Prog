if [ -f "file.sh" ]; then
  echo 'file.sh is indeed a regular file'
fi


for filename in *; do
  if [ -f $filename ]; then
    echo -n `ls -l $filename`
    echo -n " : "
    echo `file $filename | cut -d: -f2`
  else
    echo $filename is not a regular file.
  fi
done

echo
echo 

for filename in *; do
  if [ ! -f $filename ]; then
    echo $filename is not a regular file
  fi
done


