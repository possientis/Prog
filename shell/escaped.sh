echo ""

echo "This will print
as two lines."

echo "This will print \
as one line."

echo; echo

echo "============"

echo "\v\v\v\v\v\v" # \v\v\v\v\v\v literally

# use the -e option with 'echo' to print escaped character

echo "============="
echo "VERTICAL TABS"
echo -e "\v\v\v\v"  # prints 4 vertical tabes
echo "============="

echo "QUOTATION MARK"
echo -e "\042"      # prints " (quote, octal ascii character 42)
echo "============="

# The $'\X'construct makes the -e option unnecessary

echo; echo "NEWLINE and (maybe) BEEP"
echo $'\n'  # newline
echo $'\a'  # alert (beep), may only flash, not beep, depending on terminal

# =================================================================== #
# Version 2 of Bash introduced the $'\nnn' string expansion construct.
# =================================================================== #

echo "Introducing the \$\' ... \' string-expansion construct . . . "
echo ". . . featuring more quotation marks."

echo $'\t \042 \t'  # quote " framed by tabs 
# Note that \nnn is an octal value

# It also works with hexadecimal values in an $'\xhhhh'construct.
echo $'\t \x22 \t'

echo

# Assigning ASCII characters to a variable.
# ----------------------------------------
quote=$'\042'     # " assigned to a variable
echo "$quote Quoted string $quote and this lies outside the quotes."
echo

ABC=$'\101\102\103\010' # 101, 102, 103 are octal A, B, C.
echo "--$ABC--"         # --AB-- , 010 is octal backspace
echo

escape=$'\033'          # 033 is octal for escape
echo "\"escape\" echoes as $escape"
echo





