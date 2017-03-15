[[ "abcd" =~ ^a ]]
echo $? # 0 <- match


[[ "abcd" =~ a?c. ]]
echo $? # 0 <- match

