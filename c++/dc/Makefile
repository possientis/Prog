dc : main.cpp error.o lex.o table.o syn.o
	g++ -std=c++14 -o dc main.cpp error.o lex.o table.o syn.o
syn.o : syn.cpp syn.h error.h lex.h table.h
	g++ -std=c++14 -c syn.cpp
table.o : table.cpp table.h error.h
	g++ -std=c++14 -c table.cpp
lex.o : lex.cpp lex.h error.h
	g++ -std=c++14 -c lex.cpp
error.o : error.cpp error.h
	g++ -std=c++14 -c error.cpp
clean :
	rm dc error.o lex.o syn.o table.o
