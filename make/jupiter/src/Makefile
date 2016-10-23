sources = main.c
target = jupiter

all: $(target)

$(target): $(sources)
	gcc -g -O0 -o $@ $(sources)

check: all
	./jupiter | grep "Hello from .*jupiter!"
	@echo "*** ALL TESTS PASSED ***"

install: 
	install -d $(prefix)/bin
	install -m 755 jupiter $(prefix)/bin

uninstall:
	-rm $(prefix)/bin/jupiter

clean:
	-rm $(target)

.PHONY: all clean check install uninstall
