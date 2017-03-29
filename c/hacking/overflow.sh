gcc -g -o overflow overflow_example.c

./overflow $(perl -e 'print "A"x28 . "\xef\xbe\xad\xde";') 
echo "returned code = $?"

rm overflow

