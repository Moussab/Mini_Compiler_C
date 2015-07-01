%{
#include<stdio.h>
#include "2.tab.c"
#include<stdlib.h>
#include<string.h>
#include<ctype.h>
int line = 1;
typedef char UTF8;
%}


idf [a-zA-Z][_0-9a-zA-Z]*
chiffre [0-9]*
entier [-]?[0-9]|[-]?[0-9][0-9]|[-]?[0-9][0-9][0-9]|[-]?[0-9][0-9][0-9][0-9]|[-]?[0-9][0-9][0-9][0-9][0-9]
nfloat {entier}"."{chiffre}
nlong [-]?[0-9]{chiffre}{6,10}
nsimple {nfloat}[E]{chiffre}
chaindc {idf}+
biblio {chaindc}"."{chaindc}
commentaire (\/\*([^*]|\*[^/])*\*+\/)
%%
#include 		 	{return key_include;}
int 				{strcpy(yylval.mot,yytext);return key_int;}
long 				{strcpy(yylval.mot,yytext);return key_long;}
float 				{strcpy(yylval.mot,yytext);return key_float;}
simple 			{strcpy(yylval.mot,yytext);return key_simple;}
char 				{strcpy(yylval.mot,yytext);return key_char;}
entier 			{strcpy(yylval.mot,yytext);return key_entier;}
const[ \t]char|const[ \t]entier|const[ \t]simple|const[ \t]float|const[ \t]long|const[ \t]int	{strcpy(yylval.mot,yytext);return key_const;}
VOID|Void|void			{strcpy(yylval.mot,yytext);return key_void;}
{biblio}			{return key_biblio;}
IF|if|If			{return key_if;}
ELSE|Else|else 			{return key_else;}
BREAK|Break|break		{return key_break;}
FOR|For|for			{return key_for;}
WHILE|While|while		{return key_while;}
SCANF|Scanf|scanf		{return key_scanf;}
PRINTF|Printf|printf	{return key_printf;}
RETURN|Return|return	{return key_return;}
FALSE|False|false		{return key_false; }
TRUE|True|true			{return key_true;}
{commentaire}			{return key_commentaire;}
{idf} 				{  yylval.pos=TSadd(yytext);return key_idf;}
{chiffre}			{strcpy(yylval.mot,yytext); return key_chiffre;}
{entier}			{int val=atoi(yytext); if(-32768>val || val>32767){printf("OVERFLOW ligne :%d \n",yylineno);} strncpy(yylval.mot,yytext,5);return key_entier;}
{nfloat}			{strcpy(yylval.mot,yytext);return key_nfloat;}
{nlong}				{int val=atoi(yytext); if(-2147483648>val || val>2147483647){printf("OVERFLOW ligne :%d \n",yylineno);}strncpy(yylval.mot,yytext,11);return key_nlong;}
{nsimple}			{strcpy(yylval.mot,yytext);return key_nsimple;}

">" 					{strcpy(yylval.mot,yytext);return key_sup;}
"<" 					{strcpy(yylval.mot,yytext);return key_inf;}
"<=" 					{strcpy(yylval.mot,yytext);return key_infeg;}
">=" 					{strcpy(yylval.mot,yytext);return key_supeg;}
"==" 					{strcpy(yylval.mot,yytext);return key_eg;}
"!=" 					{strcpy(yylval.mot,yytext);return key_noteg;}
"!" 					{strcpy(yylval.mot,yytext);return key_not;}
"&&" 					{strcpy(yylval.mot,yytext);return key_and;}
"||" 					{strcpy(yylval.mot,yytext);return key_or;}
"+" 					{strcpy(yylval.mot,yytext);return key_add;}
"-" 					{strcpy(yylval.mot,yytext);return key_sub;}
"=" 					{strcpy(yylval.mot,yytext);return key_affec;}
"++" 					{strcpy(yylval.mot,yytext);return key_inc;}
"--" 					{strcpy(yylval.mot,yytext);return key_dec;}
"%" 					{strcpy(yylval.mot,yytext);return key_modulo;}
"*" 					{strcpy(yylval.mot,yytext);return key_mul;}
"/" 					{strcpy(yylval.mot,yytext);return key_div;}
","						{return key_verg;}
"."						{return key_point;}
";"						{return key_pverg;}
"(" 					{return key_par_ouv;}
")" 					{return key_par_fer;}
"[" 					{return key_croch_ouv;}
"]" 					{return key_croch_fer;}
"{" 					{return key_acco_ouv;}
"}" 					{return key_acco_fer;}
"#" 					{return key_dd;}

"\t"					{}
"\n"   					{ yylineno++;}
.				{}
%%



