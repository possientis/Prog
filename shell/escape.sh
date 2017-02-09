                  # simple escaping and quoting
echo \z           # z
echo \\z          # \z
echo \\\z         # \z
echo '\z'         # \z
echo '\\z'        # \\z
echo "\z"         # \z
echo "\\z"        # \z


echo
                  # command substitution
echo `echo \z`    # z
echo `echo \\z`   # z
echo `echo \\\z`  # \z    ??


variable='\'
echo "$variable"  # \

variable="\\"
echo "$variable"  # \
