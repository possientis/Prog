bin_PROGRAMS = mars
mars_SOURCES = main.c
mars_CPPFLAGS = -I$(top_srcdir)/include
mars_LDADD = ../libmar/libmars.la

check_SCRIPTS = greptest.sh
TESTS = $(check_SCRIPTS)

greptest.sh:
	echo './mars | grep "Hello from .*mars!"' > greptest.sh
	chmod +x greptest.sh

CLEANFILES = greptest.sh
