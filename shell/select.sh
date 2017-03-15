echo "Which is the odd one out?"
select name in dog cat lion tiger
do
  echo "You picked $name \($REPLY\)"
  break;
done
