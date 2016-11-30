bst : bst.t.o bst.o bstnode.o
	g++ -std=c++14 -o bst bst.t.o bst.o bstnode.o
bst.t.o : bst.t.cpp bst.h bstnode.h
	g++ -std=c++14 -c bst.t.cpp
bst.o : bst.cpp bst.h bstnode.h
	g++ -std=c++14 -c bst.cpp
bstnode.o : bstnode.cpp bstnode.h
	g++ -std=c++14 -c bstnode.cpp
clean :
	rm bst bstnode.o bst.o bst.t.o
