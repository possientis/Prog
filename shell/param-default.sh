var1=1
var2=2
# var3 is unset.
echo ${var1-$var2}  # 1
echo ${var3-$var2}  # 2
#           ^         Note the $ prefix.

echo ${username-`whoami`}
# Echoes the result of `whoami`, if variable $username is still unset.

# Whether a variable has been declared
#+ affects triggering of the default option
#+ even if the variable is null.

echo
username0=
echo "username0 has been declared, but is set to null."

echo "username0 = ${username0-`whoami`}"
# Will not echo.

echo
echo username1 has not been declared.
echo "username1 = ${username1-`whoami`}"
# Will echo.

echo
username2=
echo "username2 has been declared, but is set to null."
echo "username2 = ${username2:-`whoami`}"
#                            ^
# Will echo because of :- rather than just - in condition test.
# Compare to first instance, above.

# Once again:
variable=
# variable has been declared, but is set to null.
echo "variable-0 = ${variable-0}"
echo "variable:-1 = ${variable:-1}"
#                             ^

unset variable
echo "${variable-2}"    # 2
echo "${variable:-3}"   # 3

exit 0
