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


let "t1 = ((5 + 3, 7 - 1, 15 - 4))"
echo "t1 = $t1" # t1 = 11

let "t2= ((a = 9, 15 / 3))" # set "a" and calculate "t2"
echo "t2 = $t2  a = $a"     # t2 = 5  a = 9 

