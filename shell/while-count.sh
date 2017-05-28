count=1

while [ $count -le 5 ]; do
  echo $count
  count=$((count+1))
done
echo "Finished."
