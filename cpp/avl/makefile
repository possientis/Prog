avl : avl.t.o avl.o avlnode.o
	g++ -std=c++14 -o avl avl.t.o avl.o avlnode.o
avl.t.o : avl.t.c avl.h avlnode.h
	g++ -std=c++14 -c avl.t.c
avl.o : avl.c avl.h avlnode.h
	g++ -std=c++14 -c avl.c
avlnode.o : avlnode.c avlnode.h
	g++ -std=c++14 -c avlnode.c
clean :
	rm avl avlnode.o avl.o avl.t.o
