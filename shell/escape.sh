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


# list of files as argument(s) to a command 
file_list="/bin/cat /bin/gzip /bin/more /usr/bin/less"

ls -l /bin/ls $file_list
# what happens if we escape a space? 
# ls -l /bin/ls\ $file_list

# ls: cannot access '/bin/ls /bin/cat': No such file or directory
# -rwxr-xr-x 1 root root 98256 Mar 14  2016 /bin/gzip
# -rwxr-xr-x 1 root root 39752 Nov  8 12:29 /bin/more
# lrwxrwxrwx 1 root root     9 Nov 24 17:57 /usr/bin/less -> /bin/less

