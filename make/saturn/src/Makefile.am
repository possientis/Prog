bin_PROGRAMS = saturn
saturn_SOURCES = main.c

check_SCRIPTS = greptest.sh
TESTS = $(check_SCRIPTS)

greptest.sh:
	echo './saturn | grep "Hello from .*saturn!"' > greptest.sh
	chmod +x greptest.sh

CLEANFILES = greptest.sh
