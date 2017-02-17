if [ -t 0 ]; then # test whether file descriptor is associated with terminal
  echo "stdin is associated with a terminal device"
else
  echo "stdin is not associated with a terminal device"
fi


if [ -t 1 ]; then 
  echo "stdout is associated with a terminal device"
else
  echo "stdout is not associated with a terminal device"
fi


if [ -t 2 ]; then 
  echo "stderr is associated with a terminal device"
else
  echo "stderr is not associated with a terminal device"
fi
