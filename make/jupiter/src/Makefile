sources = main.c
target = jupiter

all: $(target)

$(target): $(sources)
	gcc -g -O0 -o $@ $(sources)

clean:
	-rm $(target)

.PHONY: all clean
