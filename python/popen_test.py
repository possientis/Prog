import subprocess

def multi(*args):
    for cmd in args:
        p = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE)
        out = p.stdout.read()
        print(out.decode('utf-8'))


if __name__ == "__main__":
    multi("df -k", "ls -l /tmp", "tail ~/.bitcoin/debug.log")
