%{
#include <string.h>
#include "absyn.h"
#include "y.tab.h"
#include "errormsg.h"

int charPos=1;
int comDepth=0;

int yywrap(void)
{
 charPos=1;
 return 1;
}

#define BUFSIZE 65536
char strbuf[BUFSIZE+1];
char *strptr = NULL;
unsigned int strlength = 0;

void setup(void)
{
	*strbuf = '\0';
	strlength = 0;
}
void appendstr(char *str)
{
	if ((strlength + strlen(str)) < BUFSIZE) {
		strcat(strbuf, str);
		strlength += strlen(str);
	}
	else{
		EM_error(EM_tokPos, "out of range");
	}
}


void adjust(void)
{
 EM_tokPos=charPos;
 charPos+=yyleng;
}

%}
%x STR
%%
[ \t]	{adjust(); continue;}
(\n|\r\n)  {adjust(); EM_newline(); continue;}
"/*"[^*]*[*]+([^*/][^*]*[*]+)*[*]*"/" {adjust();continue;}

"for"  	 {adjust(); return FOR;}
"while" {adjust(); return WHILE;}
"to"	{adjust(); return TO;}
"break" {adjust(); return BREAK;}
"let"	 {adjust(); return LET;}
"in"  {adjust(); return IN;}
"end"   {adjust(); return END;}
"function" {adjust(); return FUNCTION;}
"var"   {adjust(); return VAR;}
"type"  {adjust(); return TYPE;}
"array" {adjust(); return ARRAY;}
"if"	  {adjust(); return IF;}
"then"  {adjust(); return THEN;}
"else"  {adjust(); return ELSE;}
"do"	  {adjust(); return DO;}
"of"	  {adjust(); return OF;}
"nil"	  {adjust(); return NIL;}
[0-9]+	 {adjust(); yylval.ival=atoi(yytext); return INT;}
[a-zA-Z][a-zA-Z0-9_]*    {adjust(); yylval.sval=yytext; return ID;}
"*"   {adjust(); return TIMES;}
"/"   {adjust(); return DIVIDE;}

","	  {adjust(); return COMMA;}
":"	  {adjust(); return COLON;}
";"	  {adjust(); return SEMICOLON;}
"("	  {adjust(); return LPAREN;}
")"    {adjust(); return RPAREN;}
"["    {adjust(); return LBRACK;}
"]"   {adjust(); return RBRACK;}
"{"   {adjust(); return LBRACE;}
"}"   {adjust(); return RBRACE;}
"."   {adjust(); return DOT;}
"+"   {adjust(); return PLUS;}
"-"   {adjust(); return MINUS;}
"="   {adjust(); return EQ;}
"<>"  {adjust(); return NEQ;}
"<"   {adjust(); return LT;}
"<="  {adjust(); return LE;}
">"   {adjust(); return GT;}
">="  {adjust(); return GE;}
":="  {adjust(); return ASSIGN;}
"&"	  {adjust(); return AND;}
"|"	  {adjust(); return OR;}

\" {adjust(); BEGIN(STR); setup();}

<STR>{
	\" 			{adjust(); yylval.sval=String(strbuf); BEGIN(INITIAL); return STRING;}
	\\n			{adjust(); appendstr("\n");}
	\\t			{adjust(); appendstr("\t");}
	\\[0-9]{3}	{adjust(); appendstr(yytext);}
	\\^[GHIJLM]	{adjust(); appendstr(yytext);}
	\\\\		{adjust(); appendstr(yytext);}
	\\\"		{adjust(); appendstr(yytext);}
	\\[ \n\t\r\f]+\\ {adjust();continue;}
	\\(.|\n)	{adjust(); EM_error(EM_tokPos, "illegal token");}
	(\n|\r\n)	{adjust(); EM_error(EM_tokPos, "illegal token");}
	[^\"\\\n(\r\n)]+ 	{adjust(); appendstr(yytext);}
}
.	 {adjust(); EM_error(EM_tokPos,"illegal token");}



