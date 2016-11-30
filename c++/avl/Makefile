avl : avl.t.o avl.o avlnode.o
	g++ -std=c++14 -o avl avl.t.o avl.o avlnode.o
avl.t.o : avl.t.cpp avl.h avlnode.h
	g++ -std=c++14 -c avl.t.cpp
avl.o : avl.cpp avl.h avlnode.h
	g++ -std=c++14 -c avl.cpp
avlnode.o : avlnode.cpp avlnode.h
	g++ -std=c++14 -c avlnode.cpp
clean :
	rm avl avlnode.o avl.o avl.t.o
