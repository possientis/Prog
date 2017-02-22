
# create some test directory

echo "creating sample directory ..."
rm -rf test
mkdir test
cp col* test

echo "directory test as follows:"
tree test

echo "transfering directory to remote host ..."
tar cBvf - test | ssh pi@192.168.0.3 tar xBvpf -

echo "Checking test on remote host"
ssh pi@192.168.0.3 tree test


echo "Cleaning up test on remote host"
ssh pi@192.168.0.3 rm -rf test


