# . 
[[ "abcde" =~ . ]]
echo $? # 0 <- match

echo ${BASH_REMATCH[0]} # a



[[ "abcde" =~ ..... ]]
echo $? # 0 <- match
echo ${BASH_REMATCH[0]} # abcde

[[ "abcde" =~ ...... ]]
echo $? # 1 <- does not match 

# *
[[ "abcde" =~ (abcde)* ]]
echo $? # 0 <- match
echo ${BASH_REMATCH[0]} # abcde

[[ "" =~ (abcde)* ]]
echo $? # 0 <- match
echo ${BASH_REMATCH[0]} # ""

# []
[[ "abcde" =~ [abcde] ]]
echo $? # 0 <- match
echo ${BASH_REMATCH[0]} # a

[[ "abcde" =~ [^abcde] ]]
echo $? # 1 <- does not match

# ^
[[ "abcde" =~ b ]]
echo $? # 0 <- match
echo ${BASH_REMATCH[0]} # b


[[ "abcde" =~ ^b ]]
echo $? # 1 <- does not match


[[ "abcde" =~ ^a ]]
echo $? # 0 <- match
echo ${BASH_REMATCH[0]} # a

# $
[[ "abcde" =~ d ]]
echo $? # 0 <- match


[[ "abcde" =~ d$ ]]
echo $? # 1 <- does not match


[[ "abcde" =~ e$ ]]
echo $? # 0 <- match

# +

[[ "abcde" =~ (abcde)+ ]]
echo $? # 0 <- match

[[ "" =~ (abcde)+ ]]
echo $? # 1 <- does not match


[[ "abcde" =~ (abcdf)+ ]]
echo $? # 1 <- does not match


# ?

[[ "abcde" =~ (abc)? ]]
echo $? # 0 <- match


[[ "de" =~ (abc)? ]]
echo $? # 0 <- match

# |
[[ "abcde" =~ abc|xyz ]]
echo $? # 0 <- match


[[ "abcde" =~ abd|bde ]]
echo $? # 1 <- does not match


# ""
[[ "abcde" =~ "abcde" ]]
echo $? # 0 <- match

[[ "abcde" =~ "abcdef" ]]
echo $? # 1 <- does not match


[[ "7" =~ [0-9] ]]
echo $? # 0 <- match

pattern='\.'

[[ . =~ $pattern ]]
echo $? # 0 <- match

[[ . =~ \. ]]
echo $? # 0 <- match


[[ . =~ "$pattern" ]]
echo $? # 1 <- does not match ("\" is no longer an escape char)


[[ . =~ '\.' ]]
echo $? # 1 <- does not match ("\" is no longer an escape char) 














