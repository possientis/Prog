# only works for bash
# see let.sh of anoher use of comma

# try without the comma
for file in /{,usr/}bin/*sync
#             ^   Find all executable files ending in "sync"
#                 in /bin and /usr/bin
do
  if [ -x "$file" ]
  then
    echo $file
  fi
done

# /bin/sync
# /usr/bin/cert-sync
# /usr/bin/ipod-time-sync
# /usr/bin/purple-send-async
# /usr/bin/rsync

