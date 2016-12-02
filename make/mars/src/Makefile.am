bin_PROGRAMS = mars
mars_SOURCES = main.c
mars_CPPFLAGS = -I$(top_srcdir)/common
mars_LDADD = ../common/libmarcommon.a

check_SCRIPTS = greptest.sh
TESTS = $(check_SCRIPTS)

greptest.sh:
	echo './mars | grep "Hello from .*mars!"' > greptest.sh
	chmod +x greptest.sh

CLEANFILES = greptest.sh
