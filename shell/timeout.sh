# Works in scripts for Bash, versions 2.05b and later.

TMOUT=3

# Prompt times out at three seconds.
echo "What is your favorite song?"
echo "Quickly now, you only have $TMOUT seconds to answer!"
read song
if [ -z "$song" ]
then
  song="(no answer)"  # Default response.
fi
echo "song =$song"
exit 0
