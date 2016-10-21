sources = main.c
target = jupiter

all: $(target)

$(target): $(sources)
	gcc -g -O0 -o $@ $(sources)

check: all
	./jupiter | grep "Hello from .*jupiter!"
	@echo "*** ALL TESTS PASSED ***"

clean:
	-rm $(target)

.PHONY: all clean check
