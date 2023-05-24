# various forms of expansions are carried by bash prior to executing command
# There are 7 possible types of expansion
# On some system which support it, there is an 8th form of subsitution:

# 8. process substitution (??)

# After, the expansions havebeen performed, quote characters in the original 
# word are removed unless they have been quoted themselves:

# 9. quote removal

# Only brace expansion (1.) word splitting (6.) and pathname expansion (7.)
# can change the number of words of the expansion; other expansions expand
# a single word to a single word. The only exceptions to this are the 
# expansions of "$@" and "${name[@]}".
echo

#   - 1. brace expansion
echo "Examples of brace expansions:"
echo log{1,2,5}           # log1 log2 log5
echo log{Z..W}            # logZ logY logX logW
echo log{0..3}            # log0 log1 log2 log3
echo log\{0..3\}          # log{0..3} (not a brace expansion)
echo

# the string '${' is not considered eligible for brace expansion.
# the character '{' can be escaped with '\' as in '\{'

#   - 2. tilde expansion
echo "Examples of tilde expansions:"
echo ~                    #${HOME} 
echo ~root                # /root
echo ~john                #${HOME} 
echo path:~/Prog          # path:~/Prog (not a tilde expansion)
echo path=~Prog           # path=~Prog  (not a tilde expansion)
echo path is ~/Prog       # path is ${HOME}/Prog
echo

# tilde expansion is not performed when '~' immediately follows ':' or '='

#   - 3. parameter expansion
echo "Examples of parameter expansions:"
echo $USER                # john
echo ${USER}              # john (braces are often useful to protect var)
echo ${USER}ny            # johnny (need braces)
echo ${10}                # positional argument with 2 digits (need braces)
echo

#   - 4. arithmetic expansion
echo "Examples of arithmetic expansions:"
echo $((2+5))             # 7
echo

#   - 5. command substitution (done left to right)
echo "Examples of command substitutions:"
echo $(uname)             # Linux
echo `uname`              # Linux
echo

#   - 6. word-splitting
var="hello    word"
echo "Examples of word splittings:"
echo this is a       test: $var # this is a test: hello world
echo

#   - 7. pathmane expansion
echo "Examples of pathname expansions:"
echo a*k.sh               # asterisk.sh awk.sh
echo

# double-quotes suppresses some form of expansion but not all
# suppressed: 

#   - 1. brace expansion
echo "log{1,2,5}"         # log{1,2,5}

#   - 2. tilde expansion
echo "~"                  # ~

#   - 6. word-splitting
echo "this is a     test" # this is a     test

#   - 7. pathname expansion 
echo "a*k.sh"             # a*k.sh


# not suppressed: 

#   - 3. parameter expansion 
echo "$USER"              # john

#   - 4. arithmetic expansion
echo "$((2+5))"           # 7

#   - 5. command substitution
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

echo a   test a*k.sh ~ log{1,2,5} $(uname) $((2+5))   # a test asterisk.sh awk.sh ${HOME}log1 log2 log5 Linux 7

# single quotes: all expansions are suppressed
echo 'a   test a*k.sh ~ log{1,2,5} $(uname) $((2+5))' # a   test a*k.sh ~ log{1,2,5} $(uname) $((2+5))




