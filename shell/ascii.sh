# bash only

veg1=carrots
veg2=tomatoes

if [[ "$veg1" < "$veg2"  ]]
then
  echo "Although $veg1 precede $veg2 in the dictionary,"
  echo -n "this does not necessarily imply anything "
  echo "about my culinary preferences."
else
  echo "What kind of dictionary are you using, anyhow?"
fi
