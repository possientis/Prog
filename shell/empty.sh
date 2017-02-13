if [ -z "" ]; then
  echo "String is empty"
fi

if [ ! -n "" ]; then
  echo "String is empty"
fi

if [ -n "" ]; then
  echo "String is not empty"
else
  echo "String is empty"
fi
