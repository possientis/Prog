echo "include arith-test.sh ..."
. arith-test.sh
# This points is never reached, as previous file has an exit 0 statement
echo "include ascii.sh ..."
. ascii.sh 
