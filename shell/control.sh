
echo $'\a'    # bell works
sleep 1

echo  \a      # a (bell does not work)
echo -e \a    # a (bell does not work)

echo "\a"     # \a (bell does not work)
echo -e "\a"  # bell works
sleep 1

echo '\a'     # \a (bell does not work)
echo -e '\a'  # bell works
sleep 1



echo "abc"$'\b'd  # abd
echo -e "abc\bd"  # abd
echo -e 'abc\bd'  # abd

echo "xxx"$'\n'"xxx"
echo -e "yyy\nyyy"
echo -e 'zzz\nzzz'


echo "XXX"$'\r'"XXX"
echo -e "YYY\rYYY"
echo -e 'ZZZ\rZZZ'

echo "XXX"$'\t'"XXX"
echo -e "YYY\tYYY"
echo -e 'ZZZ\tZZZ'
