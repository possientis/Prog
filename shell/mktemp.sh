TMPFILE1=$(mktemp im1.XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX)
TMPFILE2=$(mktemp im2.XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX)

# creating signal handler to ensure files get deleted even after Ctr+C
# do not forget to use 'exit' in handler or else script will keep running
trap "rm -f $TMPFILE1 $TMPFILE2; exit 1" INT

cat /proc/interrupts > $TMPFILE1

sleep 2

cat /proc/interrupts > $TMPFILE2

diff $TMPFILE1 $TMPFILE2

rm -f $TMPFILE1 $TMPFILE2
