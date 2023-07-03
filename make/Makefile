all: guile.tmp \
	jupiter.tmp \
	saturn.tmp \
	mars.tmp


guile.tmp: 
	sh ./guile/test.sh > guile.tmp 2>&1

jupiter.tmp: 
	sh ./jupiter/test.sh > jupiter.tmp 2>&1

saturn.tmp: 
	sh ./saturn/test.sh > saturn.tmp 2>&1

mars.tmp: 
	sh ./mars/test.sh > mars.tmp 2>&1

