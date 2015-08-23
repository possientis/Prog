bst : bst.t.o bst.o bstnode.o
	g++ -std=c++14 -o bst bst.t.o bst.o bstnode.o
bst.t.o : bst.t.c bst.h bstnode.h
	g++ -std=c++14 -c bst.t.c
bst.o : bst.c bst.h bstnode.h
	g++ -std=c++14 -c bst.c
bstnode.o : bstnode.c bstnode.h
	g++ -std=c++14 -c bstnode.c
clean :
	rm bst bstnode.o bst.o bst.t.o
