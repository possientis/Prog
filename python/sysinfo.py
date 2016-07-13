#!/usr/bin/python3

# A system information gathering script

import subprocess

# Command 1
def uname_func():
    uname = "uname"
    uname_arg = "-a"
    print("Gathering system information with " +
            uname + " command:")
    subprocess.call([uname, uname_arg])


# Command 2
def disk_func():
    diskspace = "df"
    diskspace_arg = "-h"
    print("Gathering diskspace information with " +
            diskspace + " command:")
    subprocess.call([diskspace, diskspace_arg])

if __name__ == "__main__":
    uname_func()
    disk_func()

# alternative syntax
# subprocess.call("df -h",shell=True)

