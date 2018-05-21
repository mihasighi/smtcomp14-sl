#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <stdlib.h>
#include <string.h>

#include "DataTypes.h"
#include "Utilities.h"
#include "Examine.h"
#include "Parsing.h"
#include "Statistics.h"
#include "ListStatistics.h"
#include "PrintTSTP.h"
#include "Signature.h"
//-----------------------------------------------------------------------------
int ListCount(LISTNODE List,CountType WhatToCount) {

    int Counter;

    Counter = 0;
    while (List != NULL) {
//----Ignore comments
        if (LogicalAnnotatedFormula(List->AnnotatedFormula)) {
            switch (WhatToCount) {
                case nodes:
                    Counter += 1;
                    break;
                case thf_nodes:
                    if (GetSyntax(List->AnnotatedFormula) == tptp_thf) {
                        Counter += 1;
                    }
                    break;
                case tff_nodes:
                    if (GetSyntax(List->AnnotatedFormula) == tptp_tff) {
                        Counter += 1;
                    }
                    break;
                case fof_nodes:
                    if (GetSyntax(List->AnnotatedFormula) == tptp_fof) {
                        Counter += 1;
                    }
                    break;
                case cnf_nodes:
                    if (GetSyntax(List->AnnotatedFormula) == tptp_cnf) {
                        Counter += 1;
                    }
                    break;
                case count_horn_clauses:
                    if (HornClause(List->AnnotatedFormula)) {
                        Counter += 1;
                    }
                    break;
                case unit_formulae:
                    if (CountAnnotatedFormulaAtomsByPredicate(
List->AnnotatedFormula,"") == 1) {
                        Counter += 1;
                    }
                    break;
                case type_formulae:
                    if (GetRole(List->AnnotatedFormula,NULL) == type) {
                        Counter += 1;
                    }
                    break;
                case defn_formulae:
                    if (GetRole(List->AnnotatedFormula,NULL) == definition) {
                        Counter += 1;
                    }
                    break;
                case sequent_formulae:
                    if (LogicalAnnotatedFormula(List->AnnotatedFormula) &&
List->AnnotatedFormula->AnnotatedFormulaUnion.AnnotatedTSTPFormula.
FormulaWithVariables->Formula->Type == sequent) {
                        Counter += 1;
                    }
                    break;
                case count_rr_clauses:
                    if (RangeRestrictedClause(List->AnnotatedFormula)) {
                        Counter += 1;
                    }
                    break;
                case atoms:
                    Counter += CountAnnotatedFormulaAtomsByPredicate(
List->AnnotatedFormula,"");
                    break;
                case equality_atoms:
                    Counter += CountAnnotatedFormulaAtomsByPredicate(
List->AnnotatedFormula,"=");
                    break;
                case variable_atoms:
                    Counter += CountAnnotatedFormulaAtomsByPredicate(
List->AnnotatedFormula,"VARIABLE");
                    break;
                case literal_count:
                    if (GetSyntax(List->AnnotatedFormula) == tptp_cnf) {
                        Counter += CountAnnotatedFormulaAtomsByPredicate(
List->AnnotatedFormula,"");
                    }
                    break;
                case terms:
                    Counter += CountAnnotatedFormulaTerms(List->
AnnotatedFormula);
                    break;
                case count_variables:
                    Counter += CountAnnotatedFormulaUniqueVariables(List->
AnnotatedFormula);
                    break;
                case count_singletons:
                    Counter += CountAnnotatedFormulaSingletons(List->
AnnotatedFormula);
                    break;
                case count_formula_depth:
                    Counter += AnnotatedFormulaDepth(List->AnnotatedFormula);
                    break;
                case count_term_depth:
                    Counter += SumAnnotatedFormulaTermDepth(List->
AnnotatedFormula);
                    break;
                default:
                    printf("ERROR: Don't know what to count in list\n");
                    return(-1);
                    break;
            }
        }
        List = List->Next;
    }
    
    return(Counter);
}
//-----------------------------------------------------------------------------
int HeadListCount(HEADLIST HeadListHead,CountType WhatToCount) {

    int Counter;

    Counter = 0;
    while (HeadListHead != NULL) {
        if (HeadListHead->TheList != NULL) {
            Counter += ListCount(HeadListHead->TheList,WhatToCount);
        }
        HeadListHead = HeadListHead->Next;
    }

    return(Counter);
}
//-----------------------------------------------------------------------------
int ListMaximal(LISTNODE List,MaximizeType WhatToMaximize) {

    int Maximal;

    Maximal = -1;
    while (List != NULL) {
//----Ignore comments
        if (LogicalAnnotatedFormula(List->AnnotatedFormula)) {
            switch (WhatToMaximize) {
                case literals:
                    Maximal = MaximumOfInt(Maximal,
CountAnnotatedFormulaAtomsByPredicate(List->AnnotatedFormula,""));
                    break;
                case term_depth:
                    Maximal = MaximumOfInt(Maximal,
MaxAnnotatedFormulaTermDepth(List->AnnotatedFormula));
                    break;
                case formula_depth:
                    Maximal = MaximumOfInt(Maximal,AnnotatedFormulaDepth(
List->AnnotatedFormula));
                    break;
                default:
                    printf("ERROR: Unknown thing to maximize in list\n");
                    return(-1);
                    break;
            }
        }
        List = List->Next;
    }

    return(Maximal);
}
//-----------------------------------------------------------------------------
int HeadListMaximal(HEADLIST HeadListHead,MaximizeType WhatToMaximize) {

    int Maximal;
    int NextMaximal;

    Maximal = -1;
    while (HeadListHead != NULL) {
        if (HeadListHead->TheList != NULL) {
            NextMaximal = ListMaximal(HeadListHead->TheList,WhatToMaximize);
        } else {
            NextMaximal = -1;
        }
        Maximal = MaximumOfInt(NextMaximal,Maximal);
        HeadListHead = HeadListHead->Next;
    }   
    
    return(Maximal);
}
//-----------------------------------------------------------------------------
void AnalyseSymbolList(char * SymbolList,double * NumberOfSymbols,
double * NumberOfArity0,double * MinArity,double * MaxArity) {

    char * SymbolRecord;
    char * RecordRestart;
    char * SymbolField;
    char * FieldRestart;
    int Arity;

    *NumberOfSymbols = 0;
    *NumberOfArity0 = 0;
    *MinArity = -1;
    *MaxArity = -1;

    SymbolRecord = strtok_r(SymbolList,"\n",&RecordRestart);
    while (SymbolRecord != NULL) {
//DEBUG printf("Symbol is %s\n",SymbolRecord);
        (*NumberOfSymbols)++;
        SymbolField = strtok_r(SymbolRecord,"/",&FieldRestart);
        SymbolField = strtok_r(NULL,"/",&FieldRestart);
        Arity = atoi(SymbolField);
        if (Arity == 0) {
            (*NumberOfArity0)++;
        }
        if (*MinArity == -1 || Arity < *MinArity) {
            *MinArity = Arity;
        }
        if (*MaxArity == -1 || Arity > *MaxArity) {
            *MaxArity = Arity;
        }
        SymbolRecord = strtok_r(NULL,"\n",&RecordRestart);
    }
}
//-----------------------------------------------------------------------------
void GetListSymbolUsageStatistics(HEADLIST HeadList,
double * NumberOfPredicates,double * NumberOfPropositions,
double * MinPredicateArity,double * MaxPredicateArity,
double * NumberOfFunctors,double * NumberOfConstants,
double * MinFunctorArity, double * MaxFunctorArity) {

    char * PredicateCollector;
    char * FunctorCollector;
    char * OneUsage;
    char * FunctorsStart;
    int PredicateCollectorLength = STRINGLENGTH;
    int FunctorCollectorLength = STRINGLENGTH;
    LISTNODE ListNode;

    PredicateCollector = (char *)Malloc(sizeof(String));
    strcpy(PredicateCollector,"");
    FunctorCollector = (char *)Malloc(sizeof(String));
    strcpy(FunctorCollector,"");

//----Go down list collecting
    while (HeadList != NULL) {
        ListNode = HeadList->TheList;
        OneUsage = NULL;
        GetListOfAnnotatedFormulaSymbolUsage(ListNode,&OneUsage,&FunctorsStart);
        ExtendString(&FunctorCollector,FunctorsStart,&FunctorCollectorLength);
        *FunctorsStart = '\0';
        ExtendString(&PredicateCollector,OneUsage,&PredicateCollectorLength);
        Free((void **)&OneUsage);
        HeadList = HeadList->Next;
    }

    NormalizeSymbolUsage(FunctorCollector);
    NormalizeSymbolUsage(PredicateCollector);
//DEBUG printf("PREDICATES\n%sFUNCTORS\n%s\n",PredicateCollector,FunctorCollector);
    AnalyseSymbolList(FunctorCollector,NumberOfFunctors,NumberOfConstants,
MinFunctorArity,MaxFunctorArity);
    AnalyseSymbolList(PredicateCollector,NumberOfPredicates,
NumberOfPropositions,MinPredicateArity,MaxPredicateArity);

    Free((void **)&FunctorCollector);
    Free((void **)&PredicateCollector);
}
//-----------------------------------------------------------------------------
void GetListConnectiveUsageStatistics(HEADLIST HeadList,
double * NumberOfConnectives,double * NumberOfNegations,
double * NumberOfDisjunctions,double * NumberOfConjunctions,
double * NumberOfEquivalences,double * NumberOfImplications,
double * NumberOfReverseImplications,double * NumberOfXORs,
double * NumberOfNORs,double * NumberOfNANDs,double * NumberOfUniversals,
double * NumberOfExistentials,double * NumberOfPIs,double * NumberOfSIGMAs,
double * NumberOfApplications,double * NumberOfEquations,
double * NumberOfGlobalTypeDecs,double * NumberOfGlobalDefns,
double * NumberOfTypeConnectives,
double * NumberOfMAPARROWs,double * NumberOfXPRODs,double * NumberOfUNIONs,
double * NumberOfLambdas,
double * NumberOfTypedVariables,double * NumberOfDefinedVariables,
double * NumberOfPIVariables,double * NumberOfSIGMAVariables,
double * NumberOfDescriptionVariables,double * NumberOfChoiceVariables,
double * NumberOfSubtypes) {

    LISTNODE ListNode;
    double NumberOfFormulaNegations;
    double NumberOfFormulaDisjunctions;
    double NumberOfFormulaConjunctions;
    double NumberOfFormulaEquivalences;
    double NumberOfFormulaImplications;
    double NumberOfFormulaReverseImplications;
    double NumberOfFormulaXORs;
    double NumberOfFormulaNORs;
    double NumberOfFormulaNANDs;
    double NumberOfFormulaUniversals;
    double NumberOfFormulaExistentials;
    double NumberOfFormulaPIs;
    double NumberOfFormulaSIGMAs;
    double NumberOfFormulaApplications;
    double NumberOfFormulaEquations;
    double NumberOfFormulaGlobalTypeDecs;
    double NumberOfFormulaGlobalDefns;
    double NumberOfFormulaMAPARROWs;
    double NumberOfFormulaXPRODs;
    double NumberOfFormulaUNIONs;
    double NumberOfFormulaLambdas;
    double NumberOfFormulaTypedVariables;
    double NumberOfFormulaDefinedVariables;
    double NumberOfFormulaPIVariables;
    double NumberOfFormulaSIGMAVariables;
    double NumberOfFormulaDescriptionVariables;
    double NumberOfFormulaChoiceVariables;
    double NumberOfFormulaSubtypes;

//----Initialize all counters
    *NumberOfConnectives = 0;
    *NumberOfNegations = 0;
    *NumberOfDisjunctions = 0;
    *NumberOfConjunctions = 0;
    *NumberOfEquivalences = 0;
    *NumberOfImplications = 0;
    *NumberOfReverseImplications = 0;
    *NumberOfXORs = 0;
    *NumberOfNORs = 0;
    *NumberOfNANDs = 0;
    *NumberOfUniversals = 0;
    *NumberOfExistentials = 0;
    *NumberOfPIs = 0;
    *NumberOfSIGMAs = 0;
    *NumberOfApplications = 0;
    *NumberOfEquations = 0;
    *NumberOfGlobalTypeDecs = 0;
    *NumberOfGlobalDefns = 0;
    *NumberOfConnectives = 0;
    *NumberOfMAPARROWs = 0;
    *NumberOfXPRODs = 0;
    *NumberOfUNIONs = 0;
    *NumberOfLambdas = 0;
    *NumberOfTypedVariables = 0;
    *NumberOfDefinedVariables = 0;
    *NumberOfPIVariables = 0;
    *NumberOfSIGMAVariables = 0;
    *NumberOfDescriptionVariables = 0;
    *NumberOfChoiceVariables = 0;
    *NumberOfSubtypes = 0;

//----Go down list collecting
    while (HeadList != NULL) {
        ListNode = HeadList->TheList;
        while (ListNode != NULL) {
//----Ignore comments
            if (LogicalAnnotatedFormula(ListNode->AnnotatedFormula)) {
                NumberOfFormulaNegations = 0;
                NumberOfFormulaDisjunctions = 0;
                NumberOfFormulaConjunctions = 0;
                NumberOfFormulaEquivalences = 0;
                NumberOfFormulaImplications = 0;
                NumberOfFormulaReverseImplications = 0;
                NumberOfFormulaXORs = 0;
                NumberOfFormulaNORs = 0;
                NumberOfFormulaNANDs = 0;
                NumberOfFormulaUniversals = 0;
                NumberOfFormulaExistentials = 0;
                NumberOfFormulaPIs = 0;
                NumberOfFormulaSIGMAs = 0;
                NumberOfFormulaApplications = 0;
                NumberOfFormulaEquations = 0;
                NumberOfFormulaGlobalTypeDecs = 0;
                NumberOfFormulaGlobalDefns = 0;
                NumberOfFormulaMAPARROWs = 0;
                NumberOfFormulaXPRODs = 0;
                NumberOfFormulaUNIONs = 0;
                NumberOfFormulaLambdas = 0;
                NumberOfFormulaTypedVariables = 0;
                NumberOfFormulaDefinedVariables = 0;
                NumberOfFormulaPIVariables = 0;
                NumberOfFormulaSIGMAVariables = 0;
                NumberOfFormulaDescriptionVariables = 0;
                NumberOfFormulaChoiceVariables = 0;
                NumberOfFormulaSubtypes = 0;

                GetFormulaConnectiveUsage(ListNode->AnnotatedFormula->
AnnotatedFormulaUnion.AnnotatedTSTPFormula.FormulaWithVariables->Formula,
&NumberOfFormulaNegations,&NumberOfFormulaDisjunctions,
&NumberOfFormulaConjunctions,&NumberOfFormulaEquivalences,
&NumberOfFormulaImplications,&NumberOfFormulaReverseImplications,
&NumberOfFormulaXORs,&NumberOfFormulaNORs,&NumberOfFormulaNANDs,
&NumberOfFormulaUniversals,&NumberOfFormulaExistentials,
&NumberOfFormulaPIs,&NumberOfFormulaSIGMAs,
&NumberOfFormulaApplications,&NumberOfFormulaEquations,
&NumberOfFormulaGlobalTypeDecs,&NumberOfFormulaGlobalDefns,
&NumberOfFormulaMAPARROWs,&NumberOfFormulaXPRODs,&NumberOfFormulaUNIONs,
&NumberOfFormulaLambdas,
&NumberOfFormulaTypedVariables,&NumberOfFormulaDefinedVariables,
&NumberOfFormulaPIVariables,&NumberOfFormulaSIGMAVariables,
&NumberOfFormulaDescriptionVariables,&NumberOfFormulaChoiceVariables,
&NumberOfFormulaSubtypes);

                *NumberOfConnectives += (NumberOfFormulaNegations +
NumberOfFormulaDisjunctions + NumberOfFormulaConjunctions + 
NumberOfFormulaEquivalences + NumberOfFormulaImplications +
NumberOfFormulaReverseImplications + NumberOfFormulaXORs +
NumberOfFormulaNORs + NumberOfFormulaNANDs + NumberOfFormulaPIs +
NumberOfFormulaSIGMAs + NumberOfFormulaApplications);
                *NumberOfNegations += NumberOfFormulaNegations;
                *NumberOfDisjunctions += NumberOfFormulaDisjunctions;
                *NumberOfConjunctions += NumberOfFormulaConjunctions;
                *NumberOfEquivalences += NumberOfFormulaEquivalences;
                *NumberOfImplications += NumberOfFormulaImplications;
                *NumberOfReverseImplications += 
NumberOfFormulaReverseImplications;
                *NumberOfXORs += NumberOfFormulaXORs;
                *NumberOfNORs += NumberOfFormulaNORs;
                *NumberOfNANDs += NumberOfFormulaNANDs;
                *NumberOfUniversals += NumberOfFormulaUniversals;
                *NumberOfExistentials += NumberOfFormulaExistentials;
                *NumberOfPIs += NumberOfFormulaPIs;
                *NumberOfSIGMAs += NumberOfFormulaSIGMAs;
                *NumberOfApplications += NumberOfFormulaApplications;
                *NumberOfEquations += NumberOfFormulaEquations;
                *NumberOfGlobalTypeDecs += NumberOfFormulaGlobalTypeDecs;
                *NumberOfGlobalDefns += NumberOfFormulaGlobalDefns;
                *NumberOfTypeConnectives += (NumberOfFormulaMAPARROWs +
NumberOfFormulaXPRODs + NumberOfFormulaUNIONs);
                *NumberOfMAPARROWs += NumberOfFormulaMAPARROWs;
                *NumberOfXPRODs += NumberOfFormulaXPRODs;
                *NumberOfUNIONs += NumberOfFormulaUNIONs;
                *NumberOfLambdas += NumberOfFormulaLambdas;
                *NumberOfTypedVariables += NumberOfFormulaTypedVariables;
                *NumberOfDefinedVariables += NumberOfFormulaDefinedVariables;
                *NumberOfPIVariables += NumberOfFormulaPIVariables;
                *NumberOfSIGMAVariables += NumberOfFormulaSIGMAVariables;
                *NumberOfDescriptionVariables += 
NumberOfFormulaDescriptionVariables;
                *NumberOfChoiceVariables += NumberOfFormulaChoiceVariables;
                *NumberOfSubtypes += NumberOfFormulaSubtypes;
            }
            ListNode = ListNode->Next;
        }
        HeadList = HeadList->Next;
    }
}
//-----------------------------------------------------------------------------
void GetMathmaticsUsage(LISTNODE ListHead,SIGNATURE Signature,
double * NumberOfPredicates,double * NumberOfFunctions,
double * NumberOfNumbers) {

    char* MathPredicates[] = {
        "$less/2",
        "$lesseq/2",
        "$greater/2",
        "$greatereq/2",
        "$evaleq/2",
        "$is_int/1",
        "$is_rat/1",
        "$int/0",
        "$rat/0",
        "$real/0" };
    char* MathFunctions[] = {
        "$uminus/1",
        "$sum/2",
        "$difference/2",
        "$product/2",
        "$to_int/1",
        "$to_rat/1",
        "$to_real/1" };
     
    int Index;
    String MyCopy;
    char * SymbolUsage;
    char * FunctorUsage;
    char * Symbol;
    char * Slash;
    char * EndPtr;
    int Arity;
    int Uses;

//DEBUG printf("PROGRESS: Starting GetMathmaticsUsage\n");
    *NumberOfPredicates = 0;
    for (Index=0; Index < sizeof(MathPredicates)/sizeof(char*);Index++) {
        strcpy(MyCopy,MathPredicates[Index]);
        Slash = strchr(MyCopy,'/');
        *Slash = '\0';
        Slash++;
        Arity = atoi(Slash);
        if (GetSymbolUses(Signature,predicate,MyCopy,Arity) > 0) {
            (*NumberOfPredicates)++;
        }
    }
//DEBUG printf("PROGRESS: Done predicates loop\n");
    *NumberOfFunctions = 0;
    for (Index=0; Index < sizeof(MathFunctions)/sizeof(char*);Index++) {
        strcpy(MyCopy,MathFunctions[Index]);
        Slash = strchr(MyCopy,'/');
        *Slash = '\0';
        Arity = atoi(Slash+1);
        if (GetSymbolUses(Signature,function,MyCopy,Arity) > 0) {
//----Add GetSymbolUses() to get total occurrences
            (*NumberOfFunctions)++;
        }
    }
//DEBUG printf("PROGRESS: Done functions loop\n");

    SymbolUsage = NULL;
    SymbolUsage = GetListOfAnnotatedFormulaSymbolUsage(ListHead,&SymbolUsage,
&FunctorUsage);
//DEBUG printf("PROGRESS: The symbol usage is %s\n",SymbolUsage);

    *NumberOfNumbers = 0;
    Symbol = strtok(FunctorUsage,"\n");
    while (Symbol != NULL) {
//----Search from end to avoid finding / in rational numbers (aaaargh)
//DEBUG printf("Analyse ==%s==\n",Symbol);
        Slash = strrchr(Symbol,'/');
        *Slash = '\0';
        Slash++;
//DEBUG printf("Uses %s\n",Slash);
        Uses = atoi(Slash);
        Slash = strrchr(Symbol,'/');
        *Slash = '\0';
        Slash++;
//DEBUG printf("Arity %s\n",Slash);
        Arity = atoi(Slash);
//----Numbers must have 0 arity, must be recognized as a real, or have a /
//----so they are rationals.
//DEBUG printf("Symbol %s Arity %d\n",Symbol,Arity);
        if (Arity == 0 && 
(strtod(Symbol,&EndPtr) != 0.0 || EndPtr != Symbol || 
(strchr(Symbol,'/') != NULL && Symbol[0] != '\'' && Symbol[0] != '"'))) {
            (*NumberOfNumbers)++;
//---Use this to get total occurrences ...  += Uses;
        }
        Symbol = strtok(NULL,"\n");
    }
//DEBUG printf("PROGRESS: Done number counts = %f\n",*NumberOfNumbers);

    Free((void **)&SymbolUsage);
}
//-----------------------------------------------------------------------------
//----If the signature is non-NULL use it for symbols
ListStatisticsRecordType * GetListStatistics(LISTNODE ListHead,
SIGNATURE Signature,ListStatisticsRecordType * Statistics) {

    HeadListType HeadListNode;
    double NumberOfTerms;

//----Make a single node for list of lists
    HeadListNode.TheList = ListHead;
    HeadListNode.Next = NULL;

//DEBUG printf("PROGRESS: starting\n");
    Statistics->NumberOfFormulae = HeadListCount(&HeadListNode,nodes);
    Statistics->NumberOfFOF = HeadListCount(&HeadListNode,fof_nodes);
    Statistics->NumberOfTHF = HeadListCount(&HeadListNode,thf_nodes);
    Statistics->NumberOfTFF = HeadListCount(&HeadListNode,tff_nodes);
    Statistics->NumberOfCNF = HeadListCount(&HeadListNode,cnf_nodes);
//DEBUG printf("PROGRESS: counted nodes of type\n");

    Statistics->NumberOfUnitFormulae = HeadListCount(&HeadListNode,
unit_formulae);
    Statistics->NumberOfTypeFormulae = HeadListCount(&HeadListNode,
type_formulae);
    Statistics->NumberOfDefnFormulae = HeadListCount(&HeadListNode,
defn_formulae);
    Statistics->NumberOfSequents = HeadListCount(&HeadListNode,
sequent_formulae);
//DEBUG printf("PROGRESS: counted formulae of type\n");
    Statistics->NumberOfAtoms = HeadListCount(&HeadListNode,atoms);
    Statistics->NumberOfEqualityAtoms = HeadListCount(&HeadListNode,
equality_atoms);
    Statistics->NumberOfVariableAtoms = HeadListCount(&HeadListNode,
variable_atoms);
    Statistics->NumberOfLiterals = HeadListCount(&HeadListNode,
literal_count);
//DEBUG printf("PROGRESS: counted atoms of type\n");

    Statistics->MaxFormulaDepth = HeadListMaximal(&HeadListNode,formula_depth);
    if (Statistics->NumberOfFormulae > 0) {
        Statistics->AverageFormulaDepth = HeadListCount(&HeadListNode,
count_formula_depth) / Statistics->NumberOfFormulae;
    } else {
        Statistics->AverageFormulaDepth = 0.0;
    }
//DEBUG printf("PROGRESS: got formulae depth\n");
    GetListConnectiveUsageStatistics(&HeadListNode,
&Statistics->NumberOfConnectives,
&Statistics->NumberOfNegations,&Statistics->NumberOfDisjunctions,
&Statistics->NumberOfConjunctions,&Statistics->NumberOfEquivalences,
&Statistics->NumberOfImplications,&Statistics->NumberOfReverseImplications,
&Statistics->NumberOfXORs,&Statistics->NumberOfNORs,&Statistics->NumberOfNANDs,
&Statistics->NumberOfUniversals,&Statistics->NumberOfExistentials,
&Statistics->NumberOfPIs,&Statistics->NumberOfSIGMAs,
&Statistics->NumberOfApplications,&Statistics->NumberOfEquations,
&Statistics->NumberOfGlobalTypeDecs,&Statistics->NumberOfGlobalDefns,
&Statistics->NumberOfTypeConnectives,
&Statistics->NumberOfMAPARROWs,&Statistics->NumberOfXPRODs,
&Statistics->NumberOfUNIONs,&Statistics->NumberOfLambdas,
&Statistics->NumberOfTypedVariables,&Statistics->NumberOfDefinedVariables,
&Statistics->NumberOfPIVariables,&Statistics->NumberOfSIGMAVariables,
&Statistics->NumberOfDescriptionVariables,&Statistics->NumberOfChoiceVariables,
&Statistics->NumberOfSubtypes);
//DEBUG //DEBUG printf("PROGRESS: counted connectives\n");

//----For THF = is a binary op, so for mixed add them on.
    Statistics->NumberOfEqualityAtoms += Statistics->NumberOfEquations;
    Statistics->NumberOfAtoms += Statistics->NumberOfEquations;

    Statistics->NumberOfHornClauses = HeadListCount(&HeadListNode,
count_horn_clauses);
// BUG HERE FOR STICKSEL EXAMPLES
    Statistics->NumberOfRRClauses = HeadListCount(&HeadListNode,
count_rr_clauses);
    Statistics->MaxClauseSize = HeadListMaximal(&HeadListNode,literals);
    if (Statistics->NumberOfAtoms > 0) {
        Statistics->AverageClauseSize = Statistics->NumberOfLiterals /
Statistics->NumberOfCNF;
    } else {
        Statistics->AverageClauseSize = 0.0;
    }
//DEBUG printf("PROGRESS: counted THF and CNF formula types\n");

    if (Signature != NULL) {
//DEBUG printf("PROGRESS: Getting predicate symbol statistics from signature\n");
        GetSignatureSymbolUsageStatistics(Signature->Predicates,
&Statistics->NumberOfPredicates,&Statistics->NumberOfPropositions,
&Statistics->MinPredicateArity,&Statistics->MaxPredicateArity);
//DEBUG printf("PROGRESS: Getting function symbol statistics from signature\n");
        GetSignatureSymbolUsageStatistics(Signature->Functions,
&Statistics->NumberOfFunctors,&Statistics->NumberOfConstants,
&Statistics->MinFunctorArity,&Statistics->MaxFunctorArity);
    } else {
printf("Getting symbol statistics from formulae\n");
        GetListSymbolUsageStatistics(&HeadListNode,
&Statistics->NumberOfPredicates,&Statistics->NumberOfPropositions,
&Statistics->MinPredicateArity,&Statistics->MaxPredicateArity,
&Statistics->NumberOfFunctors,&Statistics->NumberOfConstants,
&Statistics->MinFunctorArity,&Statistics->MaxFunctorArity);
    }
//DEBUG printf("PROGRESS: counted predicates and functions\n");
    Statistics->NumberOfVariables = HeadListCount(&HeadListNode,
count_variables);
    Statistics->NumberOfSingletons = HeadListCount(&HeadListNode,
count_singletons);
//DEBUG printf("PROGRESS: counted variables\n");
    Statistics->MaxTermDepth = HeadListMaximal(&HeadListNode,term_depth);
    if ((NumberOfTerms = HeadListCount(&HeadListNode,terms)) > 0) {
        Statistics->AverageTermDepth = HeadListCount(&HeadListNode,
count_term_depth) / NumberOfTerms;
    } else {
        Statistics->AverageTermDepth = 0.0;
    }
//DEBUG printf("PROGRESS: got term depth\n");

//----Statistics for mathematics
    GetMathmaticsUsage(ListHead,Signature,&Statistics->NumberOfMathPredicates,
&Statistics->NumberOfMathFunctions,&Statistics->NumberOfNumbers);
//DEBUG printf("PROGRESS: got mathematics statistics\n");

    return(Statistics);
}
//-----------------------------------------------------------------------------
void PrintMinMaxArity(FILE * Stream,double Arity) {

    if (Arity == -1) {
        fprintf(Stream,"-");
    } else {
        fprintf(Stream,"%.0f",Arity);
    }
}
//-----------------------------------------------------------------------------
void PrintListStatistics(FILE * Stream,ListStatisticsRecordType Statistics) {

    if (Statistics.NumberOfFOF > 0 || Statistics.NumberOfTHF > 0 ||
Statistics.NumberOfTFF > 0) {
        fprintf(Stream,
"%% Syntax   : Number of formulae    : %4.0f (%4.0f unit",
Statistics.NumberOfFormulae,Statistics.NumberOfUnitFormulae);
        if (Statistics.NumberOfTHF > 0 || Statistics.NumberOfTFF) {
            fprintf(Stream,";%4.0f type",Statistics.NumberOfTypeFormulae);
        }
        if (Statistics.NumberOfTHF > 0) {
            fprintf(Stream,";%4.0f defn",Statistics.NumberOfDefnFormulae);
        }
    fprintf(Stream,")\n");
    }

    if (Statistics.NumberOfCNF > 0) {
        if (Statistics.NumberOfFOF > 0 || Statistics.NumberOfTHF > 0 ||
Statistics.NumberOfTFF > 0) {
            fprintf(Stream,"%%            ");
        } else {
            fprintf(Stream,"%% Syntax   : ");
        }
        fprintf(Stream,
"Number of clauses     : %4.0f (%4.0f non-Horn;%4.0f unit;%4.0f RR)\n",
Statistics.NumberOfCNF,Statistics.NumberOfCNF-Statistics.NumberOfHornClauses,
Statistics.NumberOfUnitFormulae,Statistics.NumberOfRRClauses);
    }

    fprintf(Stream,
"%%            Number of atoms       : %4.0f (%4.0f equality",
Statistics.NumberOfAtoms,Statistics.NumberOfEqualityAtoms);
    if (Statistics.NumberOfTHF > 0) {
        fprintf(Stream,";%4.0f variable",Statistics.NumberOfVariableAtoms);
    }
    fprintf(Stream,")\n");

    if (Statistics.NumberOfFOF > 0 || Statistics.NumberOfTHF > 0 ||
Statistics.NumberOfTFF > 0) {
        fprintf(Stream,
"%%            Maximal formula depth : %4.0f (%4.0f average)\n",
Statistics.MaxFormulaDepth,Statistics.AverageFormulaDepth);
    }
    if (Statistics.NumberOfCNF > 0) {
        fprintf(Stream,
"%%            Maximal clause size   : %4.0f (%4.0f average)\n",
Statistics.MaxClauseSize,Statistics.AverageClauseSize);
    }

    if (Statistics.NumberOfFOF > 0 || Statistics.NumberOfTHF > 0 ||
Statistics.NumberOfTFF > 0) {
//----First connectives line
        fprintf(Stream,
"%%            Number of connectives : %4.0f (%4.0f   ~;%4.0f   |;%4.0f   &",
Statistics.NumberOfConnectives,Statistics.NumberOfNegations,
Statistics.NumberOfDisjunctions,Statistics.NumberOfConjunctions);
        if (Statistics.NumberOfTHF > 0) {
            fprintf(Stream,";%4.0f   @",Statistics.NumberOfApplications);
        }
        fprintf(Stream,")\n");
//----Second connectives line
        fprintf(Stream,
"%%                                         (%4.0f <=>;%4.0f  =>;%4.0f  <=;%4.0f <~>)\n",
Statistics.NumberOfEquivalences,Statistics.NumberOfImplications,
Statistics.NumberOfReverseImplications,Statistics.NumberOfXORs);
//----Third connectives line
        fprintf(Stream,
"%%                                         (%4.0f  ~|;%4.0f  ~&",
Statistics.NumberOfNORs,Statistics.NumberOfNANDs);
        if (Statistics.NumberOfTHF > 0) {
            fprintf(Stream,
";%4.0f  !!;%4.0f  ??",
Statistics.NumberOfPIs,Statistics.NumberOfSIGMAs);
        } 
        fprintf(Stream,")\n");
        if (Statistics.NumberOfTHF > 0 || Statistics.NumberOfTFF > 0) {
//----Fourth connectives line, THF and TFF only
            fprintf(Stream,
"%%            Number of type conns  : %4.0f (%4.0f   >;%4.0f   *;%4.0f   +;%4.0f  <<)\n",
Statistics.NumberOfMAPARROWs + Statistics.NumberOfXPRODs + 
Statistics.NumberOfUNIONs + Statistics.NumberOfSubtypes,
Statistics.NumberOfMAPARROWs,Statistics.NumberOfXPRODs,
Statistics.NumberOfUNIONs,Statistics.NumberOfSubtypes);
        }
    }

//----Symbols
    if (Statistics.NumberOfTHF > 0) {
        fprintf(Stream,
"%%            Number of symbols     : %4.0f (%4.0f   :)\n",
Statistics.NumberOfPredicates,Statistics.NumberOfGlobalTypeDecs);
//NOT USED         fprintf(Stream,
//NOT USED "%%            Number of symbols     : %4.0f (%4.0f   :;%4.0f  :=)\n",
//NOT USED Statistics.NumberOfPredicates,Statistics.NumberOfGlobalTypeDecs,
//NOT USED Statistics.NumberOfGlobalDefns);
    }

    if (Statistics.NumberOfFOF > 0 || Statistics.NumberOfCNF > 0 ||
Statistics.NumberOfTFF > 0) {
        fprintf(Stream,
"%%            Number of predicates  : %4.0f (%4.0f propositional; ",
Statistics.NumberOfPredicates,Statistics.NumberOfPropositions);
        PrintMinMaxArity(Stream,Statistics.MinPredicateArity);
        fprintf(Stream,"-");
        PrintMinMaxArity(Stream,Statistics.MaxPredicateArity);
        fprintf(Stream," arity)\n");
        fprintf(Stream,
"%%            Number of functors    : %4.0f (%4.0f constant; ",
Statistics.NumberOfFunctors,Statistics.NumberOfConstants);
        PrintMinMaxArity(Stream,Statistics.MinFunctorArity),
        fprintf(Stream,"-");
        PrintMinMaxArity(Stream,Statistics.MaxFunctorArity);
        fprintf(Stream," arity)\n");
    }

//----Variables. Fuck, watch the sgn for FOF and THF, singleton for CNF
    fprintf(Stream,
"%%            Number of variables   : %4.0f (%4.0f ",
Statistics.NumberOfVariables,Statistics.NumberOfSingletons);

    if (Statistics.NumberOfFOF > 0 || Statistics.NumberOfTHF > 0 ||
Statistics.NumberOfTFF > 0) {
        fprintf(Stream,"sgn;%4.0f   !;%4.0f   ?",
Statistics.NumberOfUniversals,Statistics.NumberOfExistentials);
        if (Statistics.NumberOfTHF > 0) {
            fprintf(Stream,";%4.0f   ^",Statistics.NumberOfLambdas);
        }
    } else {
        fprintf(Stream,"singleton");
    }
    fprintf(Stream,")\n");
    if (Statistics.NumberOfTHF > 0) {
        fprintf(Stream,
"%%                                         (%4.0f   :;%4.0f  !>;%4.0f  ?*)\n",
Statistics.NumberOfTypedVariables,Statistics.NumberOfPIVariables,
Statistics.NumberOfSIGMAVariables);
//NOT USED         fprintf(Stream,
//NOT USED "%%                                         (%4.0f   :;%4.0f  :=;%4.0f  !>;%4.0f  ?*)\n",
//NOT USED Statistics.NumberOfTypedVariables,Statistics.NumberOfDefinedVariables,
//NOT USED Statistics.NumberOfPIVariables,Statistics.NumberOfSIGMAVariables);
    }
    if (Statistics.NumberOfTHF > 0) {
        fprintf(Stream,
"%%                                         (%4.0f  @-;%4.0f  @+)\n",
Statistics.NumberOfDescriptionVariables,Statistics.NumberOfChoiceVariables);
    }

//----Terms
    if (Statistics.NumberOfFOF > 0 || Statistics.NumberOfCNF > 0 ||
Statistics.NumberOfTFF > 0) {
        fprintf(Stream,
"%%            Maximal term depth    : %4.0f (%4.0f average)\n",
Statistics.MaxTermDepth,Statistics.AverageTermDepth); 
    }

//----Mathematics
    if (Statistics.NumberOfMathPredicates > 0 ||
Statistics.NumberOfMathFunctions > 0 ||
Statistics.NumberOfNumbers > 0 ) {
        fprintf(Stream,
"%%            Arithmetic symbols    : %4.0f (%4.0f pred; %4.0f func; %4.0f numbers)\n",
Statistics.NumberOfMathPredicates + Statistics.NumberOfMathFunctions +
Statistics.NumberOfNumbers,Statistics.NumberOfMathPredicates,
Statistics.NumberOfMathFunctions,Statistics.NumberOfNumbers);
    }
}
//-----------------------------------------------------------------------------
