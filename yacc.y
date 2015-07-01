%{
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
typedef struct err{
		char *s;
		int num;
		}er;

typedef struct li { int info; struct li *svt; } elenco;
typedef struct {int pos; char info[50];elenco* true; elenco* false; } st ;
typedef struct qc { int i;char up1[50];char up2[50];char up3[50];char up4[50];} Myquad;

char temp[1000]; int indice=0;
Myquad quad[500];int quadsuiv=1 ;
char temp_value[50]="vide"; 
typedef struct elt{
		int niv;
		int nba;
		char val[20];
		int  pos;
		char nom[20];
		char type[20];
		char port[20];
		char nat[20];
		}TS;

typedef struct liste{
    int pos;
    struct liste *nxt;
}pathfinder;
void initialisation();
void Fusion(elenco ** tete1,elenco *tete2,elenco *tete3);
void creation_list(elenco **tete,int qc);
void Backpatch(int br,elenco *tete) ;
//char *CreerTemp();
void MPorte(pathfinder *liste,char * port);
void Not_declared();
void MiseATS(char * type,pathfinder *liste);
pathfinder *Insertion(pathfinder *liste, int pos);
void play();
pathfinder* Creation( int pos);
void play_quad();
void QC();
void generer_quad(char up1[20],char up2[20],char up3[20],char up4[20]);
void affiche(elenco *tet);

int iscst=0;
int isloc=0;
TS Matable[1000];
int position=0;
int ligne=1,car=0,j=0;
char *nature=NULL;
char *port=NULL;
char *type1=NULL;
char *type2=NULL;
static int count=1;

%}





%token key_idf
%token key_entier
%token key_return
%token key_include
%token key_int
%token key_long
%token key_float
%token key_simple
%token key_char
%token key_const
%token key_if
%token key_else
%token key_break
%token key_for
%token key_while
%token key_scanf
%token key_printf
%token key_void
%token key_false
%token key_true
%token key_sup
%token key_inf
%token key_infeg
%token key_supeg
%token key_eg
%token key_noteg
%token key_not
%token key_inc
%token key_dec
%token key_and
%token key_or
%token key_add
%token key_sub
%token key_affec

%token key_modulo
%token key_mul
%token key_div
%token key_verg
%token key_pverg
%token key_point
%token key_par_ouv
%token key_par_fer
%token key_croch_ouv
%token key_croch_fer
%token key_acco_ouv
%token key_acco_fer
%token key_commentaire
%token key_decaff
%token key_incaff
%token key_dd
%token key_biblio
%token key_nfloat
%token key_nlong
%token key_nsimple
%token key_chaindc
%token key_chiffre


%nonassoc IFX
%nonassoc key_else

%right key_eg
%left key_or
%left key_and
%nonassoc key_inf key_sup key_supeg key_infeg
%left key_add key_sub
%left key_mul key_div key_modulo
%left key_not





%union 
{
int 	pos;
char 	mot[20];
pathfinder *def;
int 	adress ;
st	newtype;
elenco 	next;

}

%type<mot> type key_int key_void key_char key_long key_float key_simple key_const key_affec key_or key_and key_not mulop addop relop key_mul key_div key_modulo key_sub key_entier key_true key_false key_nfloat key_nlong key_nsimple key_chaindc key_chiffre key_add key_supeg key_inf key_sup key_infeg key_eg key_noteg var 
%type<def> var_decl_list var_declaration declaration 
%type<pos> var_decl_id key_idf 
%type<adress> M
%type<newtype> expression simple_expression or_expression not_expression  prio_expression	add_expression term deb_expression factor constant N
%type<next> WHYNOT declarations expression_decl if_decl iteration_decl compose_decl
%%
program					:include_dec declaration_list
					;
include_dec				:include_dec key_include key_inf key_biblio key_sup
					|
					;
declaration_list			:declaration_list  declaration {/*GLOBAL MISE*/ if(isloc==1) MPorte($2,"GLOBAL"); isloc=0;}
					|declaration {if(isloc==1) MPorte($1,"GLOBAL"); }
					;

declaration 				:var_declaration { $$=$1; isloc=1;}
					|fun_declaration {isloc=0;}
					;

var_declaration				:type var_decl_list key_pverg {$$=$2;MiseATS($1,$2);iscst=0;}
					;

var_decl_list				:var_decl_list key_verg var_decl_id { if(iscst==1) {nature="cst";}else{nature="var";}$$=Insertion($$,$3);}
					|var_decl_id { if(iscst==1) {nature="cst";}else{nature="var";}$$=Creation($1);}
					;

var_decl_id				:key_idf {$$=$1;}
					|key_idf key_croch_ouv key_entier  key_croch_fer { $$=$1;}					
					;

fun_declaration 			:type key_idf key_par_ouv params key_par_fer declarations {nature="fct";MiseATS($1,Creation($2)); MPorte(Creation($2),"GLOBAL_F");}			
					;

type					:key_int { strcpy($$,$1);}
					|key_void { strcpy($$,$1);}
					|key_char { strcpy($$,$1);}
					|key_long { strcpy($$,$1);}
					|key_float { strcpy($$,$1);}
					|key_simple { strcpy($$,$1);}
					|key_const {iscst=1; strcpy($$,$1);}
					;




params					:declf_list
					|
					;

declf_list				:declf_list key_verg param_id 
					|param_id 
					;

param_id				:type key_idf {nature="arg";MiseATS($1,Creation($2));isloc=0;MPorte(Creation($2),"LOCAL_F");}
					|type key_idf key_croch_ouv key_entier  key_croch_fer { nature="arg";MiseATS($1,Creation($2));MPorte(Creation($2),"LOCAL_F");}	
					;

compose_decl				:key_acco_ouv WHYNOT key_acco_fer
{
$$.svt=$2.svt;
}
					;
					
WHYNOT					:WHYNOT  declarations M
{
	Backpatch($3,$2.svt);$$.svt=$2.svt;
}
					|WHYNOT var_declaration {/*LOCAL MISE*/ MPorte($2,"LOCAL");}
					|{$$.svt=NULL;}
					;

declarations				:expression_decl {$$.svt=$1.svt;}
					|compose_decl	{$$.svt=$1.svt;}
					|if_decl	{$$.svt=$1.svt;}
					|iteration_decl	{$$.svt=$1.svt;}
					|return_decl	{$$.svt=NULL;}
					|break_decl	{$$.svt=NULL;}
					|key_commentaire {$$.svt=NULL;}
					|func_dec {$$.svt=NULL;}
					;

func_dec				:key_idf key_par_ouv arg_list key_par_fer declarations
					:var key_affec key_idf key_par_ouv arg_list key_par_fer declarations {$$.svt=NULL;}
					;

arg_list				:arg_list key_verg key_idf 
					|key_idf
					|
					;

expression_decl				:expression key_pverg 
{

	$$.svt=$1.false;
}
					|key_pverg {$$.svt=NULL;}
					;

if_decl					:key_if key_par_ouv expression key_par_fer M declarations %prec IFX 
{

	Backpatch($5,$3.true);
	Fusion(&$$.svt,$3.false,NULL);
}
					|key_if key_par_ouv expression key_par_fer M declarations key_else M N declarations 
{
	Backpatch($5,$3.true);
	Backpatch($8+1,$3.false);
	Fusion(&$3.false,$9.false,NULL);
	Backpatch($8,$3.false);
	Fusion(&$$.svt,$3.false,NULL);
	elenco *p;
	p=(elenco *)malloc(sizeof(elenco));
	p=NULL;
	//Fusion(&$$.svt,$10.svt,p);
}
					;


iteration_decl		:key_while key_par_ouv M expression key_par_fer M declarations
{
	Backpatch($6,$4.true);
	;$$.svt=$4.false;
	generer_quad( "","","BR",""); 
	QC();
	sprintf(quad[quadsuiv-1].up4,"%d",$3);
}
					|key_for key_par_ouv key_idf key_affec constant key_pverg M simple_expression key_pverg M expression  key_par_fer M N declarations
{
	Backpatch($13+1,$8.true);
	generer_quad( "","","BR",""); 
	QC();
	sprintf(quad[quadsuiv-1].up4,"%d",$10);
	/*generer_quad( "","","BR",""); 
	QC();
	sprintf(quad[quadsuiv-1].up4,"%d",$7);
	*/;$$.svt=$8.false;
	sprintf(quad[$13].up4,"%d",$7);
}
				;

return_decl				:key_return key_pverg
					|key_return expression key_pverg
					;

break_decl				:key_break key_pverg
					;


//////////////////////////////////////////////////////////////////////////////
expression 				:var key_affec expression 
{
	//sprintf(temp_value,"T%d",count++);
	generer_quad($2,$1,$3.info,"");
	QC();
	strcpy($$.info,$1);
	$$.true=$3.true; $$.false=$3.false;

}
					|var key_dec
{
	sprintf(temp_value,"T%d",count++);
	generer_quad("-",$1,"1",temp_value);
	QC();
	strcpy($$.info,temp_value);
	$$.true=NULL; $$.false=NULL;
}
					|var key_inc
{
	sprintf(temp_value,"T%d",count++);
	generer_quad("+",$1,"1",temp_value);
	QC();
	strcpy($$.info,temp_value);
	$$.true=NULL; $$.false=NULL;
}
					|simple_expression
	{
	$$.true=$1.true; $$.false=$1.false;
	strcpy($$.info,$1.info);
	}
					;

var					:key_idf { strcpy($$,Matable[$1].nom); }
					|key_idf key_croch_ouv expression  key_croch_fer {strcpy($$,Matable[$1].nom);}
					;

simple_expression			:simple_expression key_or M or_expression 
	{
	Backpatch($3,$1.false);
	$$.false=$4.false;
	Fusion(&$$.true,$1.true,$4.true);

	sprintf(temp_value,"T%d",count++);
	generer_quad($2,$1.info,$4.info,temp_value);
	QC();
	strcpy($$.info,temp_value);

	generer_quad($2,$1.info,$4.info,"");
	QC();	
	generer_quad("","","BR","");	
	QC();
	creation_list(&$$.true,quadsuiv-2) ; 
	creation_list(&$$.false,quadsuiv-1) ;
	}
					|or_expression 
	{$$.true=$1.true; $$.false=$1.false;
	strcpy($$.info,$1.info);	
	}
					;

or_expression				:or_expression key_and M not_expression
	{printf("9\n");
	Backpatch($3,$1.true);
	$$.true=$4.true;
	Fusion(&$$.false,$1.false,$4.false);

	sprintf(temp_value,"T%d",count++);
	generer_quad($2,$1.info,$4.info,temp_value);
	QC();
	strcpy($$.info,temp_value);

	generer_quad($2,$1.info,$4.info,"");
	QC();	
	generer_quad("","","BR","");	
	QC();
	creation_list(&$$.true,quadsuiv-2) ; 
	creation_list(&$$.false,quadsuiv-1) ;

	}
					|not_expression
	{
	$$.true=$1.true; $$.false=$1.false;
	strcpy($$.info,$1.info);
	}
					;

not_expression				:key_not not_expression 
	{
	$$.true=$2.false; $$.false=$2.true;
	sprintf(temp_value,"T%d",count++);
	generer_quad($1,"",$2.info,temp_value);
	QC();	
	strcpy($$.info,temp_value);
	}
					|prio_expression	
	{
	$$.true=$1.true; $$.false=$1.false;
	strcpy($$.info,$1.info);	
	}
					;

prio_expression				:add_expression relop add_expression
{
	sprintf(temp_value,"T%d",count++);
	//generer_quad($2,$1.info,$3.info,temp_value);
	//QC();	
	strcpy($$.info,temp_value);
	generer_quad($2,$1.info,$3.info,"");
	QC();	
	generer_quad("","","BR","");	
	QC();
	creation_list(&$$.true,quadsuiv-2) ; 
	creation_list(&$$.false,quadsuiv-1) ;


	
}
					|add_expression
	{
	strcpy($$.info,$1.info);
		$$.true=$1.true; $$.false=$1.false;
	}
					;

relop	 				:key_supeg {strcpy($$,$1); }
					|key_inf {strcpy($$,$1); }
					|key_sup {strcpy($$,$1); }
					|key_infeg {strcpy($$,$1); }
					|key_eg {strcpy($$,$1); }
					|key_noteg {strcpy($$,$1); }
					;
//////////////////////////////////////////////////////////////////////////////////////////////
add_expression				:add_expression addop term
	{
	

	sprintf(temp_value,"T%d",count++);

	generer_quad($2,$1.info,$3.info,temp_value);
	QC();	
	strcpy($$.info,temp_value);
	$$.true=$1.true; $$.false=$1.false;
	
	}
					|term
	{
	strcpy($$.info,$1.info);
	$$.true=$1.true; $$.false=$1.false;
	
	}
					;

addop					:key_add {strcpy($$,$1); }
					|key_sub {strcpy($$,$1); }
					;

term					:term mulop deb_expression 
	{
	sprintf(temp_value,"T%d",count++);
	generer_quad($2,$1.info,$3.info,temp_value);	
	QC();
	strcpy($$.info,temp_value);

	$$.true=$1.true; $$.false=$1.false;
	}
					|deb_expression 
	{
	strcpy($$.info,$1.info);
	$$.true=$1.true; $$.false=$1.false;

	}
					;

mulop					:key_mul	{strcpy($$,$1);}
					|key_div	{strcpy($$,$1);}
					|key_modulo	{strcpy($$,$1);}
					;

deb_expression				:key_sub deb_expression 
	{
	sprintf(temp_value,"T%d",count++);

	generer_quad($1,"",$2.info,temp_value);	
	strcpy($$.info,temp_value);
	QC();
	$$.true=$2.true; $$.false=$2.false;
	}
					|factor
	{
	$$.true=$1.true; $$.false=$1.false;
	strcpy($$.info,$1.info);

	}
					;

factor					:key_par_ouv expression key_par_fer 
{

	$$.true=$2.true; $$.false=$2.false;
	strcpy($$.info,$2.info);
}
					|var	
{

	strcpy($$.info,$1);

}
					|constant {strcpy($$.info,$1.info);}
					;

constant				:key_entier	{strcpy($$.info,$1);}	
					|key_true	{strcpy($$.info,$1);}
					|key_false	{strcpy($$.info,$1);}	
					|key_nfloat	{strcpy($$.info,$1);}
					|key_nlong	{strcpy($$.info,$1);}
					|key_nsimple	{strcpy($$.info,$1);}
					|key_chaindc	{strcpy($$.info,$1);}
					|key_chiffre	{strcpy($$.info,$1);}
					;

M : 
{ $$=quadsuiv; }
 ;
N : 
{	generer_quad("","","BR","");	
	QC();
	creation_list(&$$.false,quadsuiv-1) ;$$.true=NULL; }
;	

%%


int main(int argc, char *argv[])
{


yyin=fopen("test","r");
//initialisation();
 yyparse(); 
 yylex();
Not_declared();
play();
play_quad();
return 0;
}
 ///////////////////////////////////////////// 

void affiche(elenco *tet)
{
elenco *p;
for(p=tet;p!=NULL;p=p->svt) printf("voila %d \n",p->info);

}

void Fusion(elenco ** tete1,elenco *tete2,elenco *tete3)
{elenco *p;

for(p=tete2;p->svt!=NULL;p=p->svt);
p->svt=tete3;
*tete1=tete2;
}


void Backpatch(int br,elenco *tete) 
{
elenco *p;  
for(p=tete;p!=NULL;p=p->svt) 
sprintf(quad[p->info].up4,"%d",br); 

}


void creation_list(elenco **tete,int qc)
{
elenco *p;
p=(elenco *)malloc(sizeof(elenco));
p->info=qc;
p->svt=NULL;
*tete=p;
}

/*
char* CreerTemp() 
{
static int count=1;
char* temp=(char*)malloc(sizeof(char)*5);
sprintf(temp,"T%d",count++);
return temp;
}
*/

void QC()
{
quadsuiv++;
}

void generer_quad(char up1[50],char up2[50],char up3[50],char up4[50])
{
quad[quadsuiv].i=quadsuiv;
strcpy(quad[quadsuiv].up1,up1);
strcpy(quad[quadsuiv].up2,up2);
strcpy(quad[quadsuiv].up3,up3);
strcpy(quad[quadsuiv].up4,up4);
}

void initialisation()
{
int i=0;
for(i;i<500-1;i++)
{
strcpy(quad[i].up1,"1");
strcpy(quad[i].up2,"vide");
strcpy(quad[i].up3,"vide");
strcpy(quad[i].up4,"vide");
}

}

void play_quad()
{
char a[5],b[5],c[5],d[5],e[5];
strcpy(a,"Num");
strcpy(b,"Ope");
strcpy(c,"Opr1");
strcpy(d,"Opr2");
strcpy(e,"Resu");
int i=1;
printf("\x1B[35m\n\n----------------TABLE DES QUADRUPLETS---\n");
printf("%5s   | %5s   |%5s   |%5s   |%5s  \n",a,b,c,d,e);
printf("%5c   | %5c   |%5c   |%5c   |%5c  \n",45,45,45,45,45);
for(i;i<quadsuiv;i++)
{
printf("%5d   | %5s   |%5s   |%5s   |%5s  \n",quad[i].i,quad[i].up1,quad[i].up2,quad[i].up3,quad[i].up4);

}

printf("%5d   | %5c   |%5c   |%5c   |%5c  \n\x1B[0m",quadsuiv,45,45,45,45);

}

void play()
{
char a[5],b[5],c[5],d[5],e[5];
strcpy(a,"Pos");
strcpy(b,"Nom");
strcpy(c,"Type");
strcpy(d,"Nat");
strcpy(e,"Porté");

printf("\x1B[36m\n\n----------------TABLE DES SYMBOLES----------\n");
printf("%7s   | %7s   |%7s   |%7s   |%7s  \n",a,b,c,d,e);
printf("%7c   | %7c   |%7c   |%7c   |%7c  \n",45,45,45,45,45);
int z;
for (z=0;z<position;z++)
{
printf("%7d   | %7s   |%7s   |%7s   |%7s\n",Matable[z].pos,Matable[z].nom,Matable[z].type,Matable[z].nat,Matable[z].port);

}
printf("%7c   | %7c   |%7c   |%7c   |%7c  \n",45,45,45,45,45);

}
pathfinder* Insertion(pathfinder *liste, int pos)
{
    pathfinder* nouvelElement = malloc(sizeof(pathfinder));
    nouvelElement->pos = pos;
    nouvelElement->nxt = NULL;

        pathfinder* temp=liste;
        while(temp->nxt != NULL )
        {	if(temp->pos==pos){
		    er* monerreur = malloc(sizeof(er));


			monerreur->num=0;
			monerreur->s=Matable[temp->pos].nom;
			yyerror((void *)monerreur);
			monerreur->num=1;
			monerreur->s=Matable[temp->pos].nom;
			yyerror((void *)monerreur);	}
            temp = temp->nxt;
        }
        temp->nxt = nouvelElement;
        return liste;
}


pathfinder* Creation( int pos)
{	
    pathfinder* nouvelElement = malloc(sizeof(pathfinder));
    nouvelElement->pos = pos;
    nouvelElement->nxt = NULL;

        return nouvelElement;
}


void MPorte(pathfinder *liste,char * port)
{


	char *t=NULL;
        pathfinder* temp=liste;
        while(temp->nxt != NULL)
        {
		strcpy(Matable[temp->pos].port,port);
		temp = temp->nxt;
        }

	strcpy(Matable[temp->pos].port,port);


}

void MiseATS(char * type,pathfinder *liste)
{	char *t=NULL;
        pathfinder* temp=liste;
        while(temp->nxt != NULL)
        {
		if(strcmp("",Matable[temp->pos].type)!=0){
		    er* monerreur = malloc(sizeof(er));


			monerreur->num=0;
			monerreur->s=Matable[temp->pos].nom;
			yyerror((void *)monerreur);


			monerreur->num=3;
			monerreur->s=Matable[temp->pos].nom;
			yyerror((void *)monerreur);
	 ;}
		strncpy(Matable[temp->pos].type,type,7);
		strcpy(Matable[temp->pos].nat,nature);
		//if(port!=NULL) strcpy(Matable[temp->pos].port,port);   
		temp = temp->nxt;

        }
if(strcmp("",Matable[temp->pos].type)!=0){
		    er* monerreur = malloc(sizeof(er));


			monerreur->num=0;
			monerreur->s=Matable[temp->pos].nom;
			yyerror((void *)monerreur);


			monerreur->num=3;
			monerreur->s=Matable[temp->pos].nom;
			yyerror((void *)monerreur);
	 ;}
	strncpy(Matable[temp->pos].type,type,7); 
	strcpy(Matable[temp->pos].nat,nature);
		//if(port!=NULL) strcpy(Matable[temp->pos].port,port);   

}

TSadd(char * idf){
int v=TSearch(idf);
if (v==-1)
{
	strcpy(Matable[position].nom,idf);
	Matable[position].pos=position;
	position++;
	return(position-1);
}
else{
	return v;

}


}


///////////////////////////////////////////////
int TSearch(char *chaine)
{int j;

for(j=0;j<=position;j++)
{
if(strcmp(Matable[j].nom,chaine)==0) return j;
}

return -1;
}

void Not_declared()
{int z;
for (z=0;z<position;z++)
{

if(strcmp("",Matable[z].type)==0){
		    er* monerreur = malloc(sizeof(er));
			monerreur->num=4;
			monerreur->s=Matable[z].nom;
			yyerror((void *)monerreur);

}

}
}

////////////////////////////////////////////////

yyerror(void *s) {

	er *new;
	new =(er*) s;

switch( new->num ) 
{
    case 0 :printf("\e[32m ligne :%d Erreur: redéclaration de '%s' sans lien\n",yylineno,new->s);
        break;
    case 1 :printf("\e[32m ligne :%d Erreur: déclaration précédente de '%s' existe deja\n",yylineno,new->s);
        break;
    case 2 :printf(" \e[32mligne :%d Erreur: attention: la variable non utilisé '%s' [-Wunused-variable]|\n",yylineno,new->s);
        break;
    case 3 :printf("\e[32m ligne :%d Erreur: types contradictoires de '%s'\n",yylineno,new->s);
        break;
    case 4 :printf("\e[32m Erreur: «%s» non déclaré (première utilisation dans cette fonction) \n",new->s);
        break;

    default:printf("\e[32m ligne :%d Erreur: attendu '=', ',', ';', 'asm' or '__attribut__' avant '%s'\n",yylineno,yytext);
        break;

}

//la Verification des types n'est pas necessaire dans un langage qui ne manipule pas les pointeur ! si on fait la somme d'un caractere + un chiffre il somme automatiqumenttt le chiiffre avec le code asci de caracter; 

}
         

