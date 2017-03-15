
# comma operator used to link together arithmetic operations
# All are evaluated, but only the last one is returned

let "t2 = ((a = 9, 15 / 3))"  # set a = 9 and t2 = 15/3

echo $a   # 9
echo $t2  # 5


