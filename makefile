test: lex.yy.o errormsg.o util.o y.tab.o symbol.o absyn.o table.o parsetest.o
	cc -g -o test lex.yy.o errormsg.o util.o y.tab.o symbol.o absyn.o table.o parsetest.o

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

parsetest.o: parsetest.c errormsg.h util.h
	cc -g -c parsetest.c

clean: 
	rm -f a.out *.o