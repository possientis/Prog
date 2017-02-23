# representation of numbers in different bases

# Decimal: the default
let "dec = 32"
echo "decimal number = $dec"  # 32
dec2=32

# Octal: numbers preceded by '0' (zero)
let "oct = 032" # oct=032 will be string assignment
echo "octal number = $oct"


# Hexadecimal: number preceded by '0x' or '0X'
let "hex = 0x32"  # hex=0x32 will be string assignment
echo "hexadecimal number = $hex"  # 50

echo $((0x9abc))  # 39612 
#     ^^      ^^ double parenthesis arith expansion/eval
# expresses result in decimal


# Other bases: BASE#NUMBER
# BASE between 2 and 64
# NUMBER must use symbols within the base range, see below

let "bin = 2#111100111001101"
echo "binary number = $bin"   # 31181

let "b32 = 32#77"
echo "base 32 number = $b32"  # 231

let "b64 = 64#@_"
echo "base 64 number = $b64"  # 4031
# 10 digits + 26 lowercase + 26 uppercase + @ + _

let "check = 62*64 + 63"
echo "check = $check"         # 4031

echo
echo $((36#zz)) $((2#10101010)) $((16#AF16)) $((53#1aA))
# 1295 170 44822 3375 


