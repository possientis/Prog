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
diskspace = "df"
diskspace_arg = "-h"
print("Gathering diskspace information with " +
        diskspace + " command:")
subprocess.call([diskspace, diskspace_arg])


# alternative syntax
# subprocess.call("df -h",shell=True)

