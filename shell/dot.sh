echo "echo Hello world!" > log.sh

# none of these require log.sh to be an executable file
. log.sh
sh log.sh
bash log.sh

# This however will fail without exec permissions
# ./log.sh

rm -f log.sh


