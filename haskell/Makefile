all: song.tmp \
	json.tmp \
	Logic.tmp \
	logic2.tmp \
	types.tmp \
	lisp.tmp \
	Optics.tmp \
	adh.tmp \
	adi.tmp \
	Set.tmp

song.tmp:
	sh ./song/test.sh 	> song.tmp 2>&1

json.tmp:
	sh ./json/test.sh	> json.tmp 2>&1

Logic.tmp:
	sh ./Logic/test.sh	> Logic.tmp 2>&1

logic2.tmp:
	sh ./logic2/test.sh	> logic2.tmp 2>&1

types.tmp:
	sh ./types/test.sh	> types.tmp 2>&1

lisp.tmp:
	sh ./lisp/test.sh	> lisp.tmp 2>&1

Optics.tmp:
	sh ./Optics/test.sh	> Optics.tmp 2>&1

adi.tmp:
	sh ./adi/test.sh	> adi.tmp 2>&1

adh.tmp:
	sh ./adh/test.sh	> adh.tmp 2>&1

Set.tmp:
	sh ./Set/test.sh	> Set.tmp 2>&1

