DATE=$(date)

# use the shell's 'here document' feature rather than multiple 'echo' 


cat <<EOF

Date: $DATE

The output above is from the unix date command.

It's not a very interesting command.

EOF

# marker need not be 'EOF' but should be in uppercase (convention)


cat <<HERE

This is a test: $DATE

HERE


