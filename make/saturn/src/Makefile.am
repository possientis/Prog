bin_PROGRAMS = saturn
saturn_SOURCES = main.c
saturn_CPPFLAGS = -I$(top_srcdir)/common
saturn_LDADD = ../common/libsatcommon.a

check_SCRIPTS = greptest.sh
TESTS = $(check_SCRIPTS)

greptest.sh:
	echo './saturn | grep "Hello from .*saturn!"' > greptest.sh
	chmod +x greptest.sh

CLEANFILES = greptest.sh
