var1=hello1
var2=hello2
var3=hello3

whichvar=var1

echo
echo "whichvar is $whichvar"        # whichvar is var1
echo "${whichvar} is ${!whichvar}"  # var1 is hello1
echo


echo
echo ${!var*}                       # var1 var2 var3
echo "${!var*}"                     # var1 var2 var3
echo
echo ${!var@}                       # var1 var2 var3
echo "${!var@}"                     # var1 var2 var3
echo

# hello1
# hello2
# hello3
for i in ${!var*}; do echo ${!i}; done
echo

# var1 var2 var3  (one word, can't use indirection)
for i in "${!var*}"; do echo ${i}; done
echo

# hello1
# hello2
# hello3
for i in ${!var@}; do echo ${!i}; done
echo

# Despite double quotes...
# hello1
# hello2
# hello3
for i in "${!var@}"; do echo ${!i}; done
echo

# 0 base array
array1=(abc def ghi jkl mno pqr stu vwx yza)
setvar=xxx

echo
echo ${array1[@]}     # abc def ghi jkl mno pqr stu vwx yza
echo ${!array1[@]}    # 0 1 2 3 4 5 6 7 8
echo ${!array1[*]}    # 0 1 2 3 4 5 6 7 8
echo ${!setvar[@]}    # 0 
echo ${!setvar[*]}    # 0 
echo ${!unsetvar[@]}  # 
echo ${!unsetvar[*]}  # 

# '@' allows to use double quotes and still get separate words
# 0 1 2 3 4 5 6 7 8 9 (one word)
for i in "${!array1[*]}"; do echo $i; done

# many words despite quotes
# abc 
# def 
# ghi 
# jkl 
# mno 
# pqr 
# stu 
# vwx 
# yza
for i in "${!array1[@]}"; do echo ${array1[$i]}; done






