# bash and sh
# pipe is a child process, hence cannot alter script variable

variable="initial_value"

echo "new_value" | { read variable; echo "variable = $variable"; } # new_value

echo "variable = $variable" # initial_value
