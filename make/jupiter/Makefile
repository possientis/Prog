package = jupiter
version = 1.0
tarname = $(package)
distdir = $(tarname)-$(version)
prefix=/usr/local
export prefix	# ok with GNU make, but not portable

all clean check install uninstall jupiter:
	cd src && $(MAKE) $@	# $@ references the current target

dist: $(distdir).tar.gz

$(distdir).tar.gz: $(distdir)
	tar chof - $(distdir) | gzip -9 -c > $@
	rm -rf $(distdir)

$(distdir): FORCE
	mkdir -p $(distdir)/src									# -p not portable or unsafe for parallel
	cp Makefile $(distdir)
	cp src/Makefile $(distdir)/src
	cp src/main.c $(distdir)/src

FORCE: 
	-rm $(distdir).tar.gz > /dev/null 2>&1	# leading '-' : ignore status code 
	-rm -rf $(distdir) > /dev/null 2>&1			# returned by command, ignore error

# $$ -> means shell should dereference
distcheck: dist
	gzip -cd $(distdir).tar.gz | tar xvf - 
	cd $(distdir) && $(MAKE) all
	cd $(distdir) && $(MAKE) check
	cd $(distdir) && $(MAKE) prefix=$${PWD}/_inst install
	cd $(distdir) && $(MAKE) prefix=$${PWD}/_inst uninstall
#	mkdir -p $${PWD}/$(distdir)/_inst/bin
	@remaining="`find $${PWD}/$(distdir)/_inst -type f | wc -l`"; \
	if test "$${remaining}" -ne 0; then \
		echo "*** ${remaining} file(s) remaining in stage directory!"; \
		exit 1; \
	fi
	cd $(distdir) && $(MAKE) clean
	rm -rf $(distdir)
# leading '-' suppresses stdout display (so don't get message twice for echo)
	@echo "*** Package $(distdir).tar.gz is ready for distribution."

# don't look for filesystem objects bearing these target names
.PHONY: FORCE all clean check dist distcheck install uninstall
