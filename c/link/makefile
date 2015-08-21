link : link.t.o link.o linknode.o
	g++ -std=c++14 -o link link.t.o link.o linknode.o
link.t.o : link.t.c link.h
	g++ -std=c++14 -c link.t.c
link.o : link.c link.h linknode.h
	g++ -std=c++14 -c link.c
linknode.o : linknode.c linknode.h
	g++ -std=c++14 -c linknode.c
clean :
	rm link linknode.o link.o link.t.o
