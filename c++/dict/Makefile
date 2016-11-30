dict : dict.t.o dict.o link.o linknode.o Ilinknode.o
	g++ -std=c++14 -o dict dict.t.o dict.o link.o linknode.o Ilinknode.o
dict.t.o : dict.t.c dict.h
	g++ -std=c++14 -c dict.t.c
dict.o : dict.c dict.h link.h
	g++ -std=c++14 -c dict.c
link.o : link.c link.h linknode.h
	g++ -std=c++14 -c link.c
linknode.o : linknode.c linknode.h Ilinknode.h
	g++ -std=c++14 -c linknode.c
Ilinknode.o : Ilinknode.c Ilinknode.h
	g++ -std=c++14 -c Ilinknode.c
clean :
	rm dict dict.t.o dict.o link.o linknode.o Ilinknode.o
