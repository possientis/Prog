E_BADARGS=65

case $# in
  0|1)        # The vertical bar means "or" in this context.
    echo "Usage: `basename $0` old_file_suffix new_file_suffix"
    exit $E_BADARGS # If 0 or 1 arg, then bail out.
    ;;
esac

for filename in *.$1
# Traverse list of files ending with 1st argument.
do
  mv $filename ${filename%$1}$2 # shortest match (% #), back-end (%)
  # Strip off part of filename matching 1st argument,
  #+ then append 2nd argument.
done
exit 0
