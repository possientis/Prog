# page 340 of 458
import io
import sys, os

def daemonize(stdin='/dev/null', stdout='/dev/null', stderr='/dev/null'):
    # Perform first fork
    try:
        pid = os.fork()
        if pid > 0:     # parent
            sys.exit(0)
    except OSError as e:
        sys.stderr.write("fork #1 failed: (%d) %s\n" % (e.errno, e.strerror))
        sys.exit(1)

    # child
    # Decouple from parent's environment
    os.chdir("/")
    os.umask(0)
    os.setsid()

    # Perform second fork
    try:
        pid = os.fork()
        if pid > 0:
            sys.exit(0)
    except OSError as e:
        sys.stderr.write("fork #2 failed: (%d) %s\n" % (e.errno, e.strerror))
        sys.exit(1)

    # Process is now daemonized, redirect standard file descriptors.
    for f in sys.stdout, sys.stderr: f.flush()
    si = open(stdin, 'r')
    so = open(stdout, 'ab+')
    se = open(stderr, 'ab+', 0)
    os.dup2(si.fileno(), sys.stdin.fileno())
    os.dup2(so.fileno(), sys.stdout.fileno())
    os.dup2(se.fileno(), sys.stderr.fileno())





