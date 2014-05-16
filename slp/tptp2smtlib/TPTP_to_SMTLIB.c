#include <stdio.h>
#include <assert.h>
#include <ctype.h>
#include <string.h>
#include <stdlib.h>
#include "DataTypes.h"
#include "Utilities.h"
#include "Tokenizer.h"
#include "Parsing.h"
#include "Signature.h"
#include "Examine.h"
#include "Tree.h"
#include "List.h"
#include "TreeStatistics.h"
#include "PrintTSTP.h"

int index_alpha = 0;
int index_var = 0;
int presence_const = 0;

void PrintTerm(TERM term,FILE *out) {
	if(term->Type == function) { //"variabilele" sunt constante
		//printf("%d ",(*termeni)->FlexibleArity);
		//printf("%d ",term->TheSymbol.NonVariable->Arity);
		if (term->TheSymbol.NonVariable->Arity > 0) {
			fprintf(out," ("); //t:begin
		}
		else {
			int length = strlen(term->TheSymbol.NonVariable->NameSymbol);
			char *var_int = malloc(20*sizeof(char));
			char *temp_string = malloc(1*sizeof(char));
			char *temp_string1 = malloc(7*sizeof(char));
			strncpy(temp_string,term->TheSymbol.NonVariable->NameSymbol,1);
			if (strcmp(temp_string,"x") == 0) {
				int var=atoi(strncpy(var_int,term->TheSymbol.NonVariable->NameSymbol+1,length));
				if (index_var < var ) {
					index_var = var;
				}
				//printf("%d",index_var);
			}
			if (strcmp(temp_string,"c") == 0) {
				presence_const = 1;
				strncpy(temp_string1,term->TheSymbol.NonVariable->NameSymbol,6);
				if(strcmp(temp_string,"const_") == 0)
				{
					int var=atoi(strncpy(var_int,term->TheSymbol.NonVariable->NameSymbol+6,length));
					if (index_var < var ) {
						index_var = var;
					}
				}
			}
		}
		
		if (strcmp(term->TheSymbol.NonVariable->NameSymbol,"emp")==0) {
			fprintf(out,"(ssep (pto x_emp (ref f y_emp)) (pto z_emp (ref f t_emp)))");
			//return;
		}
		else if (strcmp(term->TheSymbol.NonVariable->NameSymbol,"sep")==0) {
			fprintf(out,"ssep ");
			int i;
			TERM *termeni = term->Arguments;
			for (i=0; i<term->TheSymbol.NonVariable->Arity; i++) {
				PrintTerm(*termeni,out);
				termeni = term->Arguments+1;
			}
			fprintf(out,")"); //:ssep_end
		}
		else if (strcmp(term->TheSymbol.NonVariable->NameSymbol,"next")==0) {
			fprintf(out,"pto ");
			TERM *termeni = term->Arguments;
			PrintTerm(*termeni,out);
			fprintf(out," (ref f ");
			termeni = term->Arguments+1;
			PrintTerm(*termeni,out);
			fprintf(out,") )"); //:sref_end
			//if (term->TheSymbol.NonVariable->Arity > 0) {
			//fprintf(out," )"); //:pto_end
			//}
		}
		else if (strcmp(term->TheSymbol.NonVariable->NameSymbol,"ls")==0) {
			char buffer[50];
			sprintf( buffer, "%d", index_alpha );
			char s[55];
			char *st = "alpha";
			sprintf( s, "%s", st );
			strcat(s,buffer);
			fprintf(out,"index %s (ls ",s);
			index_alpha++;
			int i;
			TERM *termeni = term->Arguments;
			for (i=0; i<term->TheSymbol.NonVariable->Arity; i++) {
				PrintTerm(*termeni,out);
				termeni = term->Arguments+1;
			}
			fprintf(out,"))"); //:index_end
		}
		else {
			fprintf(out,"%s ",term->TheSymbol.NonVariable->NameSymbol); //Variable->VariableName->NameSymbol);
		}
		
	}
}

void PrintFormula(FORMULA form,FILE *out);

void PrintNegFormula(FORMULA form,FILE *out) {
	
	//atomic formula: negation of an equality
	if (form->Type == atom) { //atom_f->Type 
		//printf("atom ");
		//fprintf(out,"(distinct ");
		TERM atom_form = form->FormulaUnion.Atom;
		if (atom_form->Type == predicate && strcmp(atom_form->TheSymbol.NonVariable->NameSymbol,"=")==0) {
			fprintf(out,"(distinct ");
			//printf("%d ",atom_form->TheSymbol.NonVariable->Arity);
			TERM *termeni = atom_form->Arguments;
			int i;
			for (i=0; i<atom_form->TheSymbol.NonVariable->Arity; i++) {
				PrintTerm(*termeni,out);
				termeni=atom_form->Arguments+1;
			}
			/*while (termeni != NULL) {
			 //printf("%d ",(*termeni)->Type);
			 if ((*termeni)->Type == function) { //"variabilele" sunt constante
			 printf("%s ",(*termeni)->TheSymbol.NonVariable->NameSymbol); //Variable->VariableName->NameSymbol);
			 }
			 termeni = (*termeni)->Arguments;
			 }*/
			fprintf(out,")");
		}
	}
	
	
	//negation of an equality
	if (form->Type==unary) {
		//printf("negation ");
		UnaryFormulaType uform = form->FormulaUnion.UnaryFormula;
		if (uform.Connective == negation) {
			//printf("(not ");
			FORMULA atom_f = uform.Formula;
			
			PrintFormula (atom_f,out);
			
			//printf(")");
		}
	}
	
	//conjunction 
	if (form->Type == binary) {
		BinaryFormulaType bform = form->FormulaUnion.BinaryFormula;
		if (bform.Connective == disjunction) {
			fprintf(out,"(and ");
			FORMULA atom_left = bform.LHS;
			PrintNegFormula (atom_left,out);
			FORMULA atom_right = bform.RHS;
			PrintNegFormula (atom_right,out);
			fprintf(out,")");
			
		}
	}
}


void PrintFormula(FORMULA form,FILE *out) {
	
	//atomic formula
	if (form->Type == atom) { //atom_f->Type 
		//printf("atom ");
		TERM atom_form = form->FormulaUnion.Atom;
		if (atom_form->Type == predicate) {
			//printf("predicate ");
			if (strcmp(atom_form->TheSymbol.NonVariable->NameSymbol,"heap")==0) {
				fprintf(out,"    (tobool ");
			}
			else {
				fprintf(out,"(%s ",atom_form->TheSymbol.NonVariable->NameSymbol);
			}
			//printf("%d ",atom_form->TheSymbol.NonVariable->Arity);
			TERM *termeni = atom_form->Arguments;
			int i;
			for (i=0; i<atom_form->TheSymbol.NonVariable->Arity; i++) {
				PrintTerm(*termeni,out);
				termeni=atom_form->Arguments+1;
			}
			/*while (termeni != NULL) {
			 //printf("%d ",(*termeni)->Type);
			 if ((*termeni)->Type == function) { //"variabilele" sunt constante
			 printf("%s ",(*termeni)->TheSymbol.NonVariable->NameSymbol); //Variable->VariableName->NameSymbol);
			 }
			 termeni = (*termeni)->Arguments;
			 }*/
			fprintf(out,")\n");
		}
	}
	
	
	//negation of an equality
	if (form->Type==unary) {
		//printf("negation ");
		UnaryFormulaType uform = form->FormulaUnion.UnaryFormula;
		if (uform.Connective == negation) {
			//fprintf(out,"    (not ");
			FORMULA atom_f = uform.Formula;
			if (atom_f->Type == atom) { //atom_f->Type
				//printf("atom ");
				TERM atom_form = atom_f->FormulaUnion.Atom;
				if (atom_form->Type == predicate) {
					//printf("predicate ");
					if (strcmp(atom_form->TheSymbol.NonVariable->NameSymbol,"=")==0) {
						fprintf(out,"(distinct "); //,atom_form->TheSymbol.NonVariable->NameSymbol);
					}
					//printf("%d ",atom_form->TheSymbol.NonVariable->Arity);
					TERM *termeni = atom_form->Arguments;
					int i;
					for (i=0; i<atom_form->TheSymbol.NonVariable->Arity; i++) {
						PrintTerm(*termeni,out);
						termeni=atom_form->Arguments+1;
					}
					/*while (termeni != NULL) {
					 //printf("%d ",(*termeni)->Type);
					 if ((*termeni)->Type == function) { //"variabilele" sunt constante
					 printf("%s ",(*termeni)->TheSymbol.NonVariable->NameSymbol); //Variable->VariableName->NameSymbol);
					 }
					 termeni = (*termeni)->Arguments;
					 }*/
					fprintf(out,")\n");
				}
			}
			//PrintFormula (atom_f,out);

			//fprintf(out,"    )\n");
		}
	}
	
	//conjunction 
	if (form->Type == binary) {
		BinaryFormulaType bform = form->FormulaUnion.BinaryFormula;
		if (bform.Connective == conjunction) {
			fprintf(out,"    (and ");
			FORMULA atom_left = bform.LHS;
			PrintFormula (atom_left,out);
			FORMULA atom_right = bform.RHS;
			PrintFormula (atom_right,out);
			fprintf(out,"    )\n");
			
		}
	}
}

void PrintAllFormulas(ROOTLIST r,FILE *out,TreeStatisticsRecordType Statistics){
/*	if (Statistics.NumberOfCNF > 2)
		fprintf(out,"(assert\n  (and \n");
	else
		fprintf(out,"(assert\n ");*/
	fprintf(out,"(assert\n  (and \n    (= nil nil)\n");
	while (r != NULL) {
		TREENODE t = r->TheTree;
		ANNOTATEDFORMULA f = t->AnnotatedFormula;
		if (f->Syntax == tptp_cnf) {
			AnnotatedFormulaUnionType temp = f->AnnotatedFormulaUnion;
			AnnotatedTSTPFormulaType aft = temp.AnnotatedTSTPFormula;
			if (aft.Status != axiom) {
				/*if (aft.Status==hypothesis) {
					fprintf(out,"    ( ");
				}*/
				FORMULAWITHVARIABLES form = aft.FormulaWithVariables;
				if (aft.Status==negated_conjecture) {
					//if (Statistics.NumberOfCNF > 2)
					fprintf(out,"  )\n)\n(assert\n  (not\n    ");
					//else
					//fprintf(out,")\n(assert\n  (not\n    ");
					PrintNegFormula(form->Formula,out);
				}
				//printf("this is good: %s ",aft.Name);
				else {
					PrintFormula(form->Formula,out);
				}
				
				//fprintf(out,") \n");
				if (aft.Status==negated_conjecture) {
					fprintf(out,"  ))\n");
				}
			}
		}
		//printf("%d\n",t->Visited);
		r = r->Next;
	}	
	
}


//-----------------------------------------------------------------------------
int main(int argc, char *argv[]) {

    LISTNODE Head;
    SIGNATURE Signature;
    ROOTLIST RootListHead;
    TreeStatisticsRecordType Statistics;

    Signature = NewSignature();
    SetNeedForNonLogicTokens(0);
    Head = ParseFileOfFormulae(argv[1],NULL,Signature,1,NULL);

//    PrintListOfAnnotatedTSTPNodes(stdout,Signature,Head,tptp,1);

printf("about to build root list\n");
    RootListHead = BuildRootList(Head);
printf("built root list\n");
    PrintRootList(stdout,RootListHead);

    if (GetTreeStatistics(RootListHead,&Statistics) != NULL) {
//DEBUG printf("got stats\n");
        PrintTreeStatistics(stdout,Statistics);
    }
	
//----Test output in postorder
//    PrintRootListAnnotatedNodesInPostOrder(stdout,RootListHead);

	FILE *fout = fopen("file_form","w");
	
	ROOTLIST r = RootListHead;
	
	PrintAllFormulas(r,fout,Statistics);
	
	fprintf(fout,"\n(check-sat)\n");
	
	fclose(fout);
	
	FILE *fdecl = fopen("file_decl","w");
	
	fprintf(fdecl,"(set-logic QF_NOLL)\n\n");
	
	fprintf(fdecl,"(declare-sort Sll_t 0)\n\n");
	
	fprintf(fdecl,"(declare-fun f () (Field Sll_t Sll_t))\n\n");
	
	fprintf(fdecl,"(define-fun ls ((?in Sll_t) (?out Sll_t)) Space\n");
	
	fprintf(fdecl,"(tospace (or (= ?in ?out)\n");
	
	fprintf(fdecl,"(exists ((?u Sll_t))\n");
	
	fprintf(fdecl,"(tobool\n");
	
	fprintf(fdecl,"(ssep (pto ?in (ref f ?u)) (ls ?u ?out)\n");
	
	fprintf(fdecl,"))))))\n\n");
	
	fprintf(fdecl,"(declare-fun nil () Sll_t)\n\n");
	
	fprintf(fdecl,"(declare-fun x_emp () Sll_t)\n");

	fprintf(fdecl,"(declare-fun y_emp () Sll_t)\n");

	fprintf(fdecl,"(declare-fun z_emp () Sll_t)\n");

	fprintf(fdecl,"(declare-fun t_emp () Sll_t)\n");
	
	int i;
	
	for (i=0; i<=index_var+4; i++) {
		fprintf(fdecl,"(declare-fun x%d () Sll_t)\n",i);
	}
	
	if(presence_const) {
		for (i=0; i<=index_var+4; i++) {
			fprintf(fdecl,"(declare-fun const_%d () Sll_t)\n",i);
		}
	}

	for (i=0; i<=index_alpha+4; i++) {
		fprintf(fdecl,"(declare-fun alpha%d () SetLoc)\n",i);
	}	
	
	fclose(fdecl);
	
	char *command = malloc(100*sizeof(char));
	sprintf(command,"cat file_decl file_form > %s",argv[2]);
	
	if (system(command) == -1){
		printf("Error writing the files\n");
	}
	
//	printf("**************** %d\n",index_var);
/*
//----Test extraction of leaves
    printf("---- Leaves ignoring duplicates ----\n");
    LeafListHead = GetLeafList(RootListHead,1);
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,LeafListHead,tptp,1);
    printf("---- Leaves not ignoring duplicates ----\n");
    LeafListHead = GetLeafList(RootListHead,0);
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,LeafListHead,tptp,1);
*/


    FreeRootList(&RootListHead,1);
    FreeListOfAnnotatedFormulae(&Head);
    FreeSignature(&Signature);
    assert(Head == NULL);

    return(0);
}
//-----------------------------------------------------------------------------