# bash interactive.sh for non interactive run
# . interactive.sh (from terminal) for interactive run

case "$-" in 
  *i*)  echo "This shell is interactive" ;;
  *)    echo "This shell is not interactive" ;;
esac

if [ -z "$PS1" ]; then  # PS1 is not set
  echo "This shell is not interactive"
else
  echo "This shell is interactive"
fi
