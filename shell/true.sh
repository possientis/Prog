true  # The "true" builtin
echo "exit status of \"true\" = $?"     # 0

false # The "false" builtin
echo "exit status of \"false\" = $?"    # 1

! true
echo "exit status of \"! true\" = $?"   # 1

# Note that the "!" needs a space between it and the command.
# !true leads to a "command not found" error
# The '!' operator prefixing a command invokes the Bash history mechanism.

! false
echo "exit status of \"! false\" = $?"  # 0

# preceding a _pipe_ with ! inverts the exit status returned

ls | bogus_command
echo $?   # 127

! ls | bogus_command
echo $?   # 0

# Note that the ! does not change the execution of the pipe.
# Only the exit status changes.
