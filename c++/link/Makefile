link : link.t.o link.o linknode.o Ilinknode.o
	g++ -std=c++14 -o link link.t.o link.o linknode.o Ilinknode.o
linknode : linknode.t.o Ilinknode.o
	g++ -std=c++14 -o linknode linknode.t.o Ilinknode.o
link.t.o : link.t.cpp link.h linknode.h
	g++ -std=c++14 -c link.t.cpp
linknode.t.o : linknode.t.cpp linknode.h
	g++ -std=c++14 -c linknode.t.cpp	
link.o : link.cpp link.h linknode.h
	g++ -std=c++14 -c link.cpp
linknode.o : linknode.cpp linknode.h Ilinknode.h
	g++ -std=c++14 -c linknode.cpp
Ilinknode.o : Ilinknode.cpp Ilinknode.h
	g++ -std=c++14 -c Ilinknode.cpp
clean :
	rm -f link linknode *.o
