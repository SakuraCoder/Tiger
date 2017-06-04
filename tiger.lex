%{
#include <string.h>
#include "absyn.h"
#include "y.tab.h"
#include "errormsg.h"
#define BUFSIZE 65535

int charPos = 1;
char strbuf[BUFSIZE+1];
char *strptr = NULL;
unsigned int strLen = 0;

int yywrap(void)
{
    charPos = 1;
    return 1;
}

void setup(void)
{
    strLen = 0;
    strbuf[0] = '\0';
}
void append(char *str)
{
    if (strLen + strlen(str) < BUFSIZE)
    {
        strcat(strbuf, str);
        strLen += strlen(str);
    }
    else
    {
        EM_error(EM_tokPos, "Out of range");
    }
}

void adjust(void)
{
    EM_tokPos = charPos;
    charPos += yyleng;
}

%}
%x STR
%%
[ \t]                                  {adjust(); continue;}
(\n|\r\n)                              {adjust(); EM_newline(); continue;}
"/*"[^*]*[*]+([^*/][^*]*[*]+)*[*]*"/"  {adjust(); continue;}
"array"    {adjust(); return ARRAY;}
"break"    {adjust(); return BREAK;}
"do"	   {adjust(); return DO;}
"end"      {adjust(); return END;}
"else"     {adjust(); return ELSE;}
"for"  	   {adjust(); return FOR;}
"function" {adjust(); return FUNCTION;}
"if"	   {adjust(); return IF;}
"in"       {adjust(); return IN;}
"let"	   {adjust(); return LET;}
"nil"	   {adjust(); return NIL;}
"of"	   {adjust(); return OF;}
"then"     {adjust(); return THEN;}
"to"	   {adjust(); return TO;}
"type"     {adjust(); return TYPE;}
"while"    {adjust(); return WHILE;}
"var"      {adjust(); return VAR;}
[0-9]+	   {adjust(); yylval.ival=atoi(yytext); return INT;}
[a-zA-Z][a-zA-Z0-9_]*    {adjust(); yylval.sval=yytext; return ID;}
"*"        {adjust(); return TIMES;}
"/"        {adjust(); return DIVIDE;}
"+"        {adjust(); return PLUS;}
"-"        {adjust(); return MINUS;}
"&"	       {adjust(); return AND;}
"|"	       {adjust(); return OR;}
","	       {adjust(); return COMMA;}
"."        {adjust(); return DOT;}
":"	       {adjust(); return COLON;}
";"	       {adjust(); return SEMICOLON;}
"("	       {adjust(); return LPAREN;}
")"        {adjust(); return RPAREN;}
"["        {adjust(); return LBRACK;}
"]"        {adjust(); return RBRACK;}
"{"        {adjust(); return LBRACE;}
"}"        {adjust(); return RBRACE;}
"="        {adjust(); return EQ;}
"<>"       {adjust(); return NEQ;}
"<"        {adjust(); return LT;}
"<="       {adjust(); return LE;}
">"        {adjust(); return GT;}
">="       {adjust(); return GE;}
":="       {adjust(); return ASSIGN;}
\" {adjust(); BEGIN(STR); setup();}

<STR>{
	\" 			     {adjust(); yylval.sval=String(strbuf); BEGIN(INITIAL); return STRING;}
	\\n			     {adjust(); append("\n");}
	\\t			     {adjust(); append("\t");}
	\\[0-9]{3}	     {adjust(); append(yytext);}
	\\[\\\"]		 {adjust(); append(yytext);}
	\\[ \n\t\r\f]+\\ {adjust(); continue;}
	\\(.|\n)	     {adjust(); EM_error(EM_tokPos, "illegal token");}
	(\n|\r\n)	     {adjust(); EM_error(EM_tokPos, "illegal token");}
	[^\"\\\n(\r\n)]+ {adjust(); append(yytext);}
}
.	        {adjust(); EM_error(EM_tokPos,"illegal token");}



