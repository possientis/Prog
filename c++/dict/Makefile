dict : dict.t.o dict.o link.o linknode.o Ilinknode.o
	g++ -std=c++14 -o dict dict.t.o dict.o link.o linknode.o Ilinknode.o
dict.t.o : dict.t.cpp dict.h
	g++ -std=c++14 -c dict.t.cpp
dict.o : dict.cpp dict.h link.h
	g++ -std=c++14 -c dict.cpp
link.o : link.cpp link.h linknode.h
	g++ -std=c++14 -c link.cpp
linknode.o : linknode.cpp linknode.h Ilinknode.h
	g++ -std=c++14 -c linknode.cpp
Ilinknode.o : Ilinknode.cpp Ilinknode.h
	g++ -std=c++14 -c Ilinknode.cpp
clean :
	rm dict dict.t.o dict.o link.o linknode.o Ilinknode.o
