dict : dict.t.o dict.o link.o
	g++ -std=c++14 -o dict dict.t.o dict.o link.o
dict.t.o : dict.t.c dict.h
	g++ -std=c++14 -c dict.t.c
dict.o : dict.c dict.h link.h
	g++ -std=c++14 -c dict.c
link.o : link.c link.h linknode.h
	g++ -std=c++14 -c link.c
clean :
	rm dict dict.t.o dict.o link.o
