device0=/dev/sda2

if [ -b "$device0" ]
then
  echo "$device0 is a block device"
fi

if [ ! -c "$device0" ]
then
  echo "$device0 is not a character device"
fi

device1=/dev/tty0

if [ -c "$device1" ]
then 
  echo "$device1 is a character device"
fi


if [ ! -b "$device1" ]
then 
  echo "$device1 is not a block device"
fi
