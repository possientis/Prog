dc : main.c error.o lex.o table.o syn.o
	g++ -std=c++14 -o dc main.c error.o lex.o table.o syn.o
syn.o : syn.c syn.h error.h lex.h table.h
	g++ -std=c++14 -c syn.c
table.o : table.c table.h error.h
	g++ -std=c++14 -c table.c
lex.o : lex.c lex.h error.h
	g++ -std=c++14 -c lex.c
error.o : error.c error.h
	g++ -std=c++14 -c error.c
clean :
	rm error.o lex.o syn.o table.o
