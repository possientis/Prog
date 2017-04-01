echo
string=01234567890abcdefgh
echo ${string:0}          # 01234567890abcdefgh , starts at 0
echo ${string:1:4}        # 1234                , ${parameter:offset:length}
echo ${string:1:(-4)}     # 1234567890abcd      , starts at 1, ends at -4 (excl)
echo ${string:1: -4}      # 1234567890abcd      , starts at 1, ends at -4 (excl)
echo ${string: -7}        # bcdefgh             , starts at -7, goes to the end
echo ${string: -7:0}      # ""                  , starts at -7 but 0 length
echo ${string: -7:2}      # bc                  , starts at -7 and 2 length
echo ${string: -7: -2}    # bcdef               , start at -7, ends at -2 (excl)
echo

echo                      # setting $1 $2 ...
set -- 01234567890abcdefgh xxx 

echo "$1"                 # 01234567890abcdefgh
echo "$2"                 # xxx
echo ${1:7}               # 7890abcdefgh        , looking at $1 from index 7 to end
echo ${1:7:0}             # ""                  , from 7 but 0 length
echo ${1:7:2}             # 78                  , from 7 and 2 length
echo ${1:7: -2}           # 7890abcdef          , from 7 to -2 (excl)
echo ${1: -7}             # bcdefgh             ; from -7 to end
echo ${1: -7:0}           # ""                  ; from -7 but 0 length
echo ${1: -7:2}           # bc                  ; from -7 and 2 length
echo ${1: -7: -2}         # bcdef               ; from -7 to -2 (excl)
echo


echo
array[0]=01234567890abcdefgh
echo ${array[0]}          # 01234567890abcdefgh
echo ${array[0]:7}        # 7890abcdefgh        ; from 7 to the end
echo ${array[0]:7:0}      # ""                  ; from 7 but 0 length
echo ${array[0]:7:2}      # 78                  ; from 7 and 2 length
echo ${array[0]:7: -2}    # 7890abcdef          ; from 7 to -2 (excl)
echo ${array[0]: -7}      # bcdefgh             ; from -7 to the end
echo ${array[0]: -7:0}    # ""                  ; from -7 but 0 length
echo ${array[0]: -7:2}    # bc                  ; from -7 and 2 length
echo ${array[0]: -7: -2}  # bcdef               ; from -7 to -2 (excl)
echo

echo
array=(0 1 2 3 4 5 6 7 8 9 0 a b c d e f g h)
echo ${array}             # 0                             ; first element
echo ${array[@]}          # 0 1 2 3 4 5 6 7 8 9 0 a b c d e f g h
echo ${array[@]:7}        # 7 8 9 0 a b c d e f g h       ; from 7 to the end
echo ${array[@]:7:0}      #                               ; from 7 but 0 length
echo ${array[@]:7:2}      # 7 8                           ; from 7 and 2 length
echo ${array[@]:7: -2}    # -2: substring expression < 0  ; illegal
echo ${array[@]: -7}      # b c d e f g h                 ; from -7 to the end
echo ${array[@]: -7:0}    #                               ; from -7 but 0 length
echo ${array[@]: -7:2}    # b c                           ; from -7 and 2 length
echo ${array[@]: -7:-2}   # -2: substring expression < 0  ; illegal
echo






