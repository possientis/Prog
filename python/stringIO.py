import io
import sys

file_like_string = io.StringIO("This is a\nmultiline string.\nreadline() \
        should see\nmultiple lines of\ninput")

for line in file_like_string.readlines():
    sys.stdout.write(line)


