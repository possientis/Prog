your_id=${USER}-on-${HOSTNAME}

echo "$your_id"

echo "Old \$PATH = $PATH"

PATH=${PATH}:/opt/bin # Add /opt/bin to $PATH for duration of script.

echo "New \$PATH = $PATH"
