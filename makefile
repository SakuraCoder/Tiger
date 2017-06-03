test: assem.o canon.o ucodegen.o printtree.o prabsyn.o types.o tree.o temp.o frame.o translate.o env.o semant.o lex.yy.o errormsg.o util.o y.tab.o symbol.o absyn.o table.o parse.o
	cc -g -o test assem.o canon.o ucodegen.o printtree.o prabsyn.o types.o tree.o temp.o frame.o translate.o env.o semant.o lex.yy.o errormsg.o util.o y.tab.o symbol.o absyn.o table.o parse.o

assem.o: assem.c 
	cc -g -c assem.c
canon.o: canon.c
	cc -g -c canon.c
ucodegen.o: ucodegen.c
	cc -g -c ucodegen.c
printtree.o: printtree.c
	cc -g -c printtree.c
prabsyn.o: prabsyn.c prabsyn.h
	cc -g -c prabsyn.c
semant.o: semant.c semant.h env.h absyn.h symbol.h util.h table.h temp.h frame.h types.h translate.h errormsg.h
	cc -g -c semant.c
env.o: env.c env.h types.h translate.h temp.h symbol.h util.h table.h
	cc -g -c env.c
translate.o: translate.c translate.h absyn.h symbol.h util.h table.h temp.h frame.h tree.h
	cc -g -c translate.c
frame.o: frame.c frame.h tree.h temp.h util.h
	cc -g -c frame.c
tree.o: tree.c tree.h temp.h symbol.h util.h table.h
	cc -g -c tree.c
temp.o: temp.c temp.h symbol.h table.h util.h
	cc -g -c temp.c

types.o: types.c types.h util.h symbol.h table.h
	cc -g -c types.c

errormsg.o: errormsg.c errormsg.h util.h
	cc -g -c errormsg.c

lex.yy.o: lex.yy.c absyn.h y.tab.h errormsg.h util.h
	cc -g -c lex.yy.c

y.tab.o: y.tab.c util.h errormsg.h absyn.h symbol.h
	cc -g -c y.tab.c

y.tab.h: y.tab.c
	
y.tab.c: tiger.grm
	bison -dt tiger.grm -o y.tab.c

lex.yy.c: tiger.lex 
	flex tiger.lex

symbol.o: symbol.c symbol.h util.h symbol.h table.h
	cc -g -c symbol.c
absyn.o: absyn.c absyn.h symbol.h util.h
	cc -g -c absyn.c

table.o: table.c table.h util.h
	cc -g -c table.c

util.o: util.c util.h
	cc -g -c util.c

parse.o: parse.c errormsg.h util.h
	cc -g -c parse.c

clean: 
	rm -f a.out *.o