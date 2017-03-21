echo 
find . -type f -name 'a*.sh' -print | xargs gzip
ls --color=auto

echo
find . -type f -name 'a*.sh.gz' -print | xargs gunzip
ls --color=auto

# you can execute tasks in parallel (FAILS)

#echo 
#find . -type f -name 'a*.sh' -print | parallel gzip
#ls --color=auto



#echo
#find . -type f -name 'a*.sh.gz' -print | parallel gunzip
#ls --color=auto
