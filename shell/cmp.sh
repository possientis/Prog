echo -n "This is a sentence" > a
echo -n "This is a sentence" > b
echo -n "This is a different sentence" > c

if cmp a b &> /dev/null # supress output
then echo "Files a and b are identical"
else echo "Files a and b are different"
fi

if diff a b &> /dev/null
then echo "Files a and b are identical"
else echo "Files a and b are different"
fi


if cmp a c &> /dev/null # supress output
then echo "Files a and c are identical"
else echo "Files a and c are different"
fi


if diff a c &> /dev/null # supress output
then echo "Files a and c are identical"
else echo "Files a and c are different"
fi


rm a b c
