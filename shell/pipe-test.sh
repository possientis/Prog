function show_input_type()
{
  [ -p /dev/fd/0 ] && echo PIPE || echo STDIN
}

show_input_type "Input"         # STDIN
echo "Input" | show_input_type  # PIPE
