# various forms of expansions are carried by bash prior to executing command
#   - word-splitting
echo this is a       test # this is a test
#   - pathmane expansion
echo a*k.sh               # asterisk.sh awk.sh
#   - tilde expansion
echo ~                    # /home/john
echo ~root                # /root
echo ~john                # /home/john
#   - brace expansion
echo log{1,2,5}           # log1 log2 log5
echo log{Z..W}            # logZ logY logX logW
echo log{0..3}            # log0 log1 log2 log3
#   - parameter expansion
echo $USER                # john
#   - arithmetic expansion
echo $((2+5))             # 7
#   - command substitution
echo $(uname)             # Linux
echo `uname`              # Linux

# double-quotes suppresses some form of expansion but not all
# suppressed: 
#   - word-splitting
echo "this is a     test" # this is a     test
#   - pathname expansion 
echo "a*k.sh"             # a*k.sh
#   - tilde expansion
echo "~"                  # ~
#   - brace expansion
echo "log{1,2,5}"         # log{1,2,5}


# not suppressed: 
#   - parameter expansion 
echo "$USER"              # john
#   - arithmetic expansion
echo "$((2+5))"           # 7
#   - command substitution
echo "$(uname)"           # Linux

# However, this is not to say that behaviour is identical
# here 'echo' command is called with 40 arguments
echo $(cal)               # March 2017 Su Mo Tu We Th Fr Sa 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
# here 'echo# command is called with a single argument
echo "$(cal)"
#       March 2017       
#     Su Mo Tu We Th Fr Sa  
#      1  2  3  4  
#      5  6  7  8  9 10 11  
#     12 13 14 15 16 17 18  
#     19 20 21 22 23 24 25  
#     26 27 28 29 30 31   

echo a   test a*k.sh ~ log{1,2,5} $(uname) $((2+5))   # a test asterisk.sh awk.sh /home/john log1 log2 log5 Linux 7

# single quotes: all expansions are suppressed
echo 'a   test a*k.sh ~ log{1,2,5} $(uname) $((2+5))' # a   test a*k.sh ~ log{1,2,5} $(uname) $((2+5))




