# various forms of expansions are carried by bash prior to executing command

# word-splitting
echo this is a       test # this is a test

# pathmane expansion
echo a*k.sh               # asterisk.sh awk.sh

# tilde expansion
echo ~                    # /home/john
echo ~root                # /root
echo ~john                # /home/john

# brace expansion
echo log{1,2,5}           # log1 log2 log5
echo log{Z..W}            # logZ logY logX logW
echo log{0..3}            # log0 log1 log2 log3

# parameter expansion
echo $USER                # john

# arithmetic expansion
echo $((2+5))             # 7

# command substitution
echo $(uname)             # Linux
echo `uname`              # Linux

#TODO
