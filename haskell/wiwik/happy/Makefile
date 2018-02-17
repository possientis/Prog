all : a.out


Syntax.o : Syntax.hs
	ghc -c Syntax.hs

Lexer.hs : Lexer.x
	alex Lexer.x

Lexer.o : Lexer.hs Syntax.o
	ghc -c Lexer.hs

Parser.hs : Parser.y
	happy Parser.y

Parser.o : Parser.hs Lexer.o Syntax.o
	ghc -c Parser.hs

Eval.o : Eval.hs Syntax.o
	ghc -c Eval.hs

a.out : Main.hs Syntax.o Eval.o Parser.o
	ghc Main.hs -o a.out
