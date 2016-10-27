sources = main.c
target = jupiter
CFLAGS = -g -O0		# debug symbol + no optimization

all: $(target)

$(target): $(sources)
	$(CC) $(CPPFLAGS) $(CFLAGS) -o $@ $(sources)

check: all
	./jupiter | grep "Hello from .*jupiter!"
	@echo "*** ALL TESTS PASSED ***"

install:
	install -d $(DESTDIR)$(bindir)
	install -m 755 jupiter $(DESTDIR)$(bindir)

uninstall:
	-rm $(DESTDIR)$(bindir)/jupiter

clean:
	-rm $(target)

.PHONY: all clean check install uninstall
