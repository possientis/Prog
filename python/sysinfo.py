#!/usr/bin/python3

# A system information gathering script

import subprocess

# Command 1
uname = "uname"
uname_arg = "-a"
print("Gathering system information with " +
        uname + " command:")
subprocess.call([uname, uname_arg])


# Command 2

