#include <stdio.h>
#include <assert.h>
#include <ctype.h>
#include <string.h>
#include <stdlib.h>
#include "DataTypes.h"
#include "Utilities.h"
#include "FileUtilities.h"
#include "Tokenizer.h"
#include "Parsing.h"
#include "Signature.h"
#include "Examine.h"
#include "Compare.h"
#include "Modify.h"
#include "List.h"
#include "Tree.h"
#include "ListStatistics.h"
#include "PrintTSTP.h"
#include "PrintDFG.h"
#include "PrintKIF.h"
#include "PrintOtter.h"
#include "PrintXML.h"
#include "PrintSMT2.h"
#include "SystemOnTPTP.h"
//-----------------------------------------------------------------------------
int main(int argc, char *argv[]) {

    LISTNODE Head;
    LISTNODE AnotherHead;
    ROOTLIST RootListHead;
    String PutNamesHere;
    String CurrentFileName;
    SIGNATURE Signature;
    ANNOTATEDFORMULA AnnotatedFormula;
    ANNOTATEDFORMULA AnotherAnnotatedFormula;
    ANNOTATEDFORMULA DuplicatedAnnotatedFormula;
    FORMULA Literal;
    FORMULA AnotherLiteral;
    String SomeString;
    char * SymbolUsage;
    char * AnotherSymbolUsage;
    char * VariablesStartHere;
    int SymbolUsageLength = STRINGLENGTH;
    int VarCount,QuantCount;
    StatusType SubStatus;
    TERM ANewTerm;
    int Positive,Negative;
    READFILE Stream;
    ListStatisticsRecordType ListStatistics;
    int Universals,Existentials;
    int NumberRemoved;
    ContextType Context;
    LISTNODE Axioms;
    LISTNODE Conjectures;
    LISTNODE Target;
    String FormulaName;
    String OutputFileName;
    int Result;
    BTREENODE BTreeRoot;
    BTREENODE * SearchResult;
    TERMArray ArrayOfInfoTERMs;
    int NumberOfTerms;
    int Index;
    SZSResultType SZS1,SZS2;
    SZSOutputType SZSO1,SZSO2;

//----One signature for all testing
    Signature = NewSignature();

//----Read from file or stdin
    SetNeedForNonLogicTokens(1);
    SetAllowFreeVariables(0);
//----Test duplicate arity warnings
    SetWarnings(1);
    if (argc > 1) {
        Head = ParseFileOfFormulae(argv[1],NULL,Signature,1,NULL);
    } else {
        Head = ParseFILEOfFormulae(stdin,Signature,1,NULL);
    }
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,Head,tptp,1);
    FreeListOfAnnotatedFormulae(&Head);
    FreeSignature(&Signature);
    return(EXIT_SUCCESS);

//-----------------------------------------------------------------------------
//----Test comparison of first two formula for being the same
    AnnotatedFormula = GetAnnotatedFormulaFromListByNumber(Head,1);
    AnotherAnnotatedFormula = GetAnnotatedFormulaFromListByNumber(Head,2);
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    PrintAnnotatedTSTPNode(stdout,AnotherAnnotatedFormula,tptp,1);
    if (SameFormulaInAnnotatedFormulae(AnnotatedFormula,
AnotherAnnotatedFormula,0,1)) {
        printf("They are identical\n");
    } else {
        if (SameFormulaInAnnotatedFormulae(AnnotatedFormula,
AnotherAnnotatedFormula,1,1)) {
            printf("They are renamings\n");
        } else {
            printf("They are quite different\n");
        }
    }
    FreeListOfAnnotatedFormulae(&Head);
    FreeSignature(&Signature);
    return(EXIT_SUCCESS);

//----Test list duplication
    AnotherHead = DuplicateListOfAnnotatedFormulae(Head,Signature);
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,AnotherHead,tptp,1);
    FreeListOfAnnotatedFormulae(&Head);
    FreeListOfAnnotatedFormulae(&AnotherHead);
    FreeSignature(&Signature);
    return(EXIT_SUCCESS);

//----Test reading header
    FreeListOfAnnotatedFormulae(&Head);
    FreeSignature(&Signature);
    SetNeedForNonLogicTokens(1);
    Head = ParseFileOfHeader(argv[1]);
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,Head,tptp,1);
    FreeListOfAnnotatedFormulae(&Head);
    return(EXIT_SUCCESS);

//----Test building root list
    RootListHead = BuildRootList(Head);
    PrintRootList(stdout,RootListHead);
    FreeRootList(&RootListHead,1);
    FreeListOfAnnotatedFormulae(&Head);
    FreeSignature(&Signature);
    return(EXIT_SUCCESS);

//----Test randomization
    RandomizeListOfAnnotatedFormulae(&Head,1);
    printf("------------ Randomized ---------------\n");
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,Head,tptp,1);
    FreeListOfAnnotatedFormulae(&Head);
    FreeSignature(&Signature);
    return(EXIT_SUCCESS);

//----Test getting root list
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,GetRootList(Head),tptp,1);
    return(EXIT_SUCCESS);

//----Test vine of lemmas extraction
    printf("---- Vine of lemmas ---\n");
    RootListHead = BuildRootList(Head);
    PrintRootList(stdout,RootListHead);
    if (GetRootLemmaList(RootListHead->TheTree,&Axioms,0)) {
        PrintListOfAnnotatedTSTPNodes(stdout,Signature,Axioms,tptp,1);
        FreeListOfAnnotatedFormulae(&Axioms);
    } else {
        printf("Could not extract vine of axioms\n");
    }
    FreeRootList(&RootListHead,1);
    FreeListOfAnnotatedFormulae(&Head);
    FreeSignature(&Signature);
    return(EXIT_SUCCESS);

//----Test dequoting
    PrintSignature(Signature);
    printf("---- Dequote ---\n");
    DequoteSymbolsInSignature(Signature);
    PrintSignature(Signature);
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,Head,tptp,1);
    FreeListOfAnnotatedFormulae(&Head);
    FreeSignature(&Signature);
    return(EXIT_SUCCESS);

//----Test aritizing
    PrintSignature(Signature);
    printf("---- Aritize ---\n");
    AritizeSymbolsInSignature(Signature);
    PrintSignature(Signature);
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,Head,tptp,1);
    FreeListOfAnnotatedFormulae(&Head);
    FreeSignature(&Signature);
    return(EXIT_SUCCESS);

//----Test expanding assumptions
    printf("---- Expand assumptions ---\n");
    ExpandListAssumptions(Head,Signature);
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,Head,tptp,1);
    FreeListOfAnnotatedFormulae(&Head);
    FreeSignature(&Signature);
    return(EXIT_SUCCESS);

//----Test formula duplication
    AnnotatedFormula = GetAnnotatedFormulaFromListByNumber(Head,1);
    if (AnnotatedFormula != NULL) {
        PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
        PrintVariableList(AnnotatedFormula->
AnnotatedFormulaUnion.AnnotatedTSTPFormula.FormulaWithVariables->Variables,
NULL);
        PrintSignature(Signature);
        DuplicatedAnnotatedFormula = DuplicateAnnotatedFormula(AnnotatedFormula,
Signature);
        PrintAnnotatedTSTPNode(stdout,DuplicatedAnnotatedFormula,tptp,1);
        PrintVariableList(DuplicatedAnnotatedFormula->
AnnotatedFormulaUnion.AnnotatedTSTPFormula.FormulaWithVariables->Variables,
NULL);
        PrintSignature(Signature);
    } else {
        printf("Could not get formula dv\n");
    }
    return(EXIT_SUCCESS);

//----Test uninterpreting of integers
    UninterpretIntegersInSignature(Signature);
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,Head,tptp,1);
    exit(EXIT_SUCCESS);

//----Test getting inference rule
    AnnotatedFormula = GetAnnotatedFormulaFromListByNumber(Head,1);
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    if ((SymbolUsage = GetSource(AnnotatedFormula)) != NULL) {
        printf("The source is ==%s==\n",SymbolUsage);
        Free((void **)&SymbolUsage);
    }
    if ((SymbolUsage = GetSourceTerm(AnnotatedFormula,NULL)) != NULL) {
        printf("The source term is ==%s==\n",SymbolUsage);
        Free((void **)&SymbolUsage);
    }
    if ((SymbolUsage = GetInferenceRule(AnnotatedFormula,NULL)) != NULL) {
        printf("The inference rule is ==%s==\n",SymbolUsage);
        Free((void **)&SymbolUsage);
    }
    if ((SymbolUsage = GetParentNames(AnnotatedFormula,NULL)) != NULL) {
        printf("The parents are ==%s==\n",SymbolUsage);
        Free((void **)&SymbolUsage);
    }
    if ((SymbolUsage = GetSourceInfoTerm(AnnotatedFormula,"introduced","status",
NULL)) != NULL) {
        printf("The status term is %s\n",SymbolUsage);
        Free((void **)&SymbolUsage);
    }
    FreeListOfAnnotatedFormulae(&Head);
    FreeSignature(&Signature);
    return(EXIT_SUCCESS);

//----Test getting nested inference info
    PrintAnnotatedTSTPNode(stdout,Head->AnnotatedFormula,tptp,1);
    NumberOfTerms = 0;
    ArrayOfInfoTERMs = GetInferenceInfoTERMs(Head->AnnotatedFormula,"assumptions",
&NumberOfTerms);
    for (Index = 0; Index < NumberOfTerms; Index++) {
        PrintTSTPTerm(stdout,ArrayOfInfoTERMs[Index],-1,1);
        printf("\n");
    }
    if (ArrayOfInfoTERMs != NULL) {
        Free((void **)&ArrayOfInfoTERMs);
    }
    return(EXIT_SUCCESS);

//----Test getting file source
    AnnotatedFormula = GetAnnotatedFormulaFromListByNumber(Head,1);
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    if (GetSource(AnnotatedFormula) != NULL) {
        printf("The source is %s\n",SomeString);
        if ((SymbolUsage = GetFileSourceNameAndNode(AnnotatedFormula,NULL)) != 
NULL) {
            printf("The file and node are %s\n",SymbolUsage);
            Free((void **)&SymbolUsage);
        } else {
            printf("No file and node\n");
        }
    } else {
        printf("No source for file and node\n");
    }
    FreeListOfAnnotatedFormulae(&Head);
    FreeSignature(&Signature);
    exit(EXIT_SUCCESS);

//----Test useful info manipulation
    AnnotatedFormula = GetAnnotatedFormulaFromListByNumber(Head,1);
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    AddUsefulInformationToAnnotatedFormula(AnnotatedFormula,Signature,
"useful(1)");
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    AddUsefulInformationToAnnotatedFormula(AnnotatedFormula,Signature,
"useful([2,two,2],2-two)");
    AddUsefulInformationToAnnotatedFormula(AnnotatedFormula,Signature,
"useful(3)");
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    if ((SymbolUsage = GetUsefulInfoTerm(AnnotatedFormula,"useful",2,NULL)) != 
NULL) {
        printf("The second useful term is %s\n",SymbolUsage);
        Free((void **)&SymbolUsage);
    }
    UpdateUsefulInformationInAnnotatedFormula(AnnotatedFormula,Signature,
"useful(4)");
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    AddUsefulInformationToAnnotatedFormula(AnnotatedFormula,Signature,
"useful(5)");
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    RemoveUsefulInformationFromAnnotatedFormula(AnnotatedFormula,Signature,
"useful");
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    FreeListOfAnnotatedFormulae(&Head);
    FreeSignature(&Signature);
    return(EXIT_SUCCESS);

//----Test sorting by useful info
    SortByUsefulInfoField(&Head,"sortby",'f',0);
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,Head,tptp,1);
    exit(EXIT_SUCCESS);

//----Test binary trees
    printf("---- Binary tree ----\n");
    BTreeRoot = ListToBTree(Head);
    PrintBTreeOfAnnotatedFormulae(BTreeRoot);
    printf("---- Search for %s\n","pel55_5");
    if ((SearchResult = GetNodeFromBTreeByAnnotatedFormulaName(&BTreeRoot,
"pel55_5")) == NULL) {
        printf("Not found\n");
    } else {
        PrintAnnotatedTSTPNode(stdout,(*SearchResult)->AnnotatedFormula,tptp,1);
    }
    FreeBTreeOfAnnotatedFormulae(&BTreeRoot);
    assert(BTreeRoot == NULL);
    FreeListOfAnnotatedFormulae(&Head);
    FreeSignature(&Signature);
    return(EXIT_SUCCESS);

//----Test negation or universal fofify
    FOFifyList(Head,universal);
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,Head,tptp,1);
    PrintSignature(Signature);
    return(EXIT_SUCCESS);

//----Look at the signature
    PrintSignature(Signature);
    FreeListOfAnnotatedFormulae(&Head);
    FreeSignature(&Signature);
    return(EXIT_SUCCESS);

//----Test external processing
    AnotherHead = ApplyExternalProgram(Head,axiom,NULL,"cat %s",Signature);
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,AnotherHead,tptp,1);
    exit(EXIT_SUCCESS);

//----Test set relationships
    AnotherHead = ParseFileOfFormulae(argv[2],NULL,Signature,1,NULL);
    printf("-------------------\n");
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,AnotherHead,tptp,1);
    printf("===================\n");
    Head = MergeInListOfAnnotatedFormulaeByFields(&Head,&AnotherHead,1,0,1);
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,Head,tptp,1);
    printf("-------------------\n");
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,AnotherHead,tptp,1);
    exit(EXIT_SUCCESS);

//----Test getting by name
    AnnotatedFormula = GetAnnotatedFormulaFromListByName(Head,"freddy");
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    exit(EXIT_SUCCESS);

//----Testing redirected printing
    PrintStringAnnotatedTSTPNode(SomeString,Head->AnnotatedFormula,tptp,1);
    printf("==%s==\n",SomeString);
    exit(EXIT_SUCCESS);

//----Test negation
    AnnotatedFormula = Head->AnnotatedFormula;
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    if (DeDoubleNegate(AnnotatedFormula)) {
        printf("Dedouble negated\n");
        PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    }
    Negate(AnnotatedFormula,1);
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    return(EXIT_SUCCESS);

//----Test selection of nodes with status
    Axioms = GetListOfAnnotatedFormulaeWithType(Head,axiom_like);
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,Axioms,tptp,1);
    return(EXIT_SUCCESS);

//----Test use of SystemOnTPTP
    if (SystemOnTPTPAvailable()) {
        Axioms = GetListOfAnnotatedFormulaeWithType(Head,axiom_like);
        printf("Axioms are ...\n");
        PrintListOfAnnotatedTSTPNodes(stdout,Signature,Axioms,tptp,1);
        Conjectures = GetListOfAnnotatedFormulaeWithType(Head,conjecture);
        Target = Conjectures;
        while (Target != NULL) {
            printf("Trying to prove %s\n",GetName(Target->AnnotatedFormula,
FormulaName));
//            strcpy(OutputFileName,FormulaName);
//            strcat(OutputFileName,".result");
//            Result = SystemOnTPTP(Axioms,Conjectures->AnnotatedFormula,
//"E---0.9","Theorem",1,"Paradox---1.3","CounterTheorem",30,">>",1,"",
//OutputFileName,OutputFileName);
            Result = SystemOnTPTP(Axioms,Conjectures->AnnotatedFormula,
"E---0.9","Theorem",1,"Paradox---1.3","CounterTheorem",30,"",1,"/tmp","output",
OutputFileName);
//            Result = SystemOnTPTP(Axioms,Conjectures->AnnotatedFormula,
//"E---0.9","Theorem",1,"Paradox---1.3","CounterTheorem",30,"",0,NULL,NULL,NULL);
            printf("The output file name is %s\n",OutputFileName);
            switch (Result) {
                case 1:
                    printf("%s is a theorem\n",FormulaName);
                    break;
                case -1:
                    printf("%s is not a theorem\n",FormulaName);
                    break;
                case 0:
                    printf("%s is unknown\n",FormulaName);
                    break;
                default:
                    CodingError("SystemOnTPTP returned something weird");
                    break;
            }
            Target = Target->Next;
        }
        FreeListOfAnnotatedFormulae(&Axioms);
        FreeListOfAnnotatedFormulae(&Conjectures);
    }
    return(EXIT_SUCCESS);

//----Test freeing
    PrintSignature(Signature);
    FreeListOfAnnotatedFormulae(&Head);
    assert(Head == NULL);
    PrintSignature(Signature);
    RemovedUnusedSymbols(Signature);
    printf("REMOVED THE UNUSED\n");
    fflush(stdout);
    PrintSignature(Signature);
    FreeSignature(&Signature);
    assert(Signature == NULL);
    return(EXIT_SUCCESS);

//----Test Foreign output
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,Head,dfg,1);
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,Head,kif,1);
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,Head,otter,1);
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,Head,xml,1);
    return(EXIT_SUCCESS);

//----Test read-free alternation
    SetNeedForNonLogicTokens(0);
    if ((Stream = OpenReadFile(argv[1],CurrentFileName)) == NULL) {
        printf("Can't open file %s\n",argv[1]);
        return(EXIT_FAILURE);
    }
    while (!CheckTokenType(Stream,endeof)) {
        printf("Start ------------------\n");
        AnnotatedFormula = ParseAndUseAnnotatedFormula(Stream,Signature);
        PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
        PrintSignature(Signature);
        printf("Free ------------------\n");
        FreeAnnotatedFormula(&AnnotatedFormula);
        PrintSignature(Signature);
        printf("End ------------------\n");
    }
    CloseReadFile(Stream);
    return(EXIT_SUCCESS);

//----Test signature iterator
    PrintSignatureTree(Signature->Predicates);
    printf("===========\n");
    ListSignatureBySearch(Signature->Predicates);
    return(EXIT_SUCCESS);

//----Test freeing
    PrintSignature(Signature);
    FreeListOfAnnotatedFormulae(&Head);
    assert(Head == NULL);
    PrintSignature(Signature);
    RemovedUnusedSymbols(Signature);
    printf("REMOVED THE UNUSED\n");
    fflush(stdout);
    PrintSignature(Signature);
    FreeSignature(&Signature);
    assert(Signature == NULL);
    return(EXIT_SUCCESS);

//----Test getting symbol usage in general
    AnnotatedFormula = GetAnnotatedFormulaFromListByNumber(Head,1);
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    SymbolUsage = (char *)Malloc(sizeof(String));
    if (GetAnnotatedFormulaSymbolUsage(AnnotatedFormula,&SymbolUsage,
&AnotherSymbolUsage) != NULL) {
        printf("The total symbol usage is \n%s and the functors are \n%s\n",
SymbolUsage,AnotherSymbolUsage);
    } else {
        printf("No total symbol usage collected\n");
    }
    Free((void **)&SymbolUsage);
    return(EXIT_SUCCESS);

//----Test internal formula copying
    AnnotatedFormula = GetAnnotatedFormulaFromListByNumber(Head,1);
    if (AnnotatedFormula != NULL) {
        PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
        PrintVariableList(AnnotatedFormula->
AnnotatedFormulaUnion.AnnotatedTSTPFormula.FormulaWithVariables->Variables,
NULL);
        PrintSignature(Signature);
        Literal = AnnotatedFormula->AnnotatedFormulaUnion.AnnotatedTSTPFormula.FormulaWithVariables->Formula->FormulaUnion.QuantifiedFormula.Formula->FormulaUnion.BinaryFormula.LHS;
        Context.Signature = Signature;
        Context.Variables = &(AnnotatedFormula->AnnotatedFormulaUnion.AnnotatedTSTPFormula.FormulaWithVariables->Variables);
        AnotherLiteral = DuplicateInternalFormulaWithVariables(
Literal,Context);
        PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
        printf("duplicate is ...\n");
        PrintTSTPFormula(stdout,AnnotatedFormula->Syntax,AnotherLiteral,0,1,
outermost,0);
        printf("\n");
        PrintVariableList(AnnotatedFormula->
AnnotatedFormulaUnion.AnnotatedTSTPFormula.FormulaWithVariables->Variables,
NULL);
        PrintSignature(Signature);
    } else {
        printf("Could not get first formula\n");
    }
    return(EXIT_SUCCESS);

//----Test variable counting
    AnnotatedFormula = GetAnnotatedFormulaFromListByNumber(Head,1);
    if (AnnotatedFormula != NULL) {
        PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,0);
        VarCount = CountVariableUsageInFormula(AnnotatedFormula->
AnnotatedFormulaUnion.AnnotatedTSTPFormula.FormulaWithVariables->Formula,
AnnotatedFormula->AnnotatedFormulaUnion.AnnotatedTSTPFormula.
FormulaWithVariables->Variables,&QuantCount);
        printf("First variable occurs %d times, plus quantified %d times\n",
VarCount,QuantCount);
    } else {
        printf("Could not get first formula\n");
    }
    return(EXIT_SUCCESS);

//----Test getting parents' names
    if (AnnotatedFormula != NULL) {
        printf("Parents are\n%s\n",GetParentNames(AnnotatedFormula,
PutNamesHere));
    } else {
        printf("Formula of that name not found\n");
    }
    return(EXIT_SUCCESS);

//----Test removal of vacuous quantifiers
    AnnotatedFormula = GetAnnotatedFormulaFromListByNumber(Head,1);
    if (AnnotatedFormula != NULL) {
        PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,0);
        PrintVariableList(AnnotatedFormula->
AnnotatedFormulaUnion.AnnotatedTSTPFormula.FormulaWithVariables->Variables,
NULL);
        PrintSignature(Signature);
        NumberRemoved = RemoveVacuousQuantifiersFromAnnotatedFormula(
AnnotatedFormula);
        PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
        PrintVariableList(AnnotatedFormula->
AnnotatedFormulaUnion.AnnotatedTSTPFormula.FormulaWithVariables->Variables,
NULL);
        PrintSignature(Signature);
        printf("%d removed\n",NumberRemoved);
    } else {
        printf("Could not get first formula\n");
    }
    return(EXIT_SUCCESS);

//----Test uniqueify variable names
    AnnotatedFormula = GetAnnotatedFormulaFromListByName(Head,"dv");
    if (AnnotatedFormula != NULL) {
        PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
        PrintSignature(Signature);
        UniqueifyVariableNames(AnnotatedFormula);
        PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
        PrintSignature(Signature);
    } else {
        printf("Could not get formula dv\n");
    }
    return(EXIT_SUCCESS);

//----Test freeing
    FreeListOfAnnotatedFormulae(&Head);
    assert(Head == NULL);
    return(EXIT_SUCCESS);

//----Test reading another file
    AnotherHead = ParseFileOfFormulae(argv[1],NULL,Signature,1,NULL);
    PrintListOfAnnotatedTSTPNodes(stdout,Signature,AnotherHead,tptp,1);
    return(EXIT_SUCCESS);

//----Test negation or universal fofify
    AnnotatedFormula = GetAnnotatedFormulaFromListByName(Head,"22");
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    if (DeDoubleNegate(AnnotatedFormula)) {
        printf("Dedouble negated\n");
        PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    }
    FOFify(AnnotatedFormula,universal);
    if (CheckAnnotatedFormula(AnnotatedFormula,tptp_cnf)) {
        FOFify(AnnotatedFormula,universal);
    } else {
        Negate(AnnotatedFormula,1);
    }
    printf("negated (FOF) or fofified (CNF)\n");
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    return(EXIT_SUCCESS);

//----Test stats
    if (GetListStatistics(Head,Signature,&ListStatistics) != NULL) {
        PrintListStatistics(stdout,ListStatistics);
    } else {
        printf("Could not get statistics\n");
    }
    FreeListOfAnnotatedFormulae(&Head);
    assert(Head == NULL);
    return(EXIT_SUCCESS);

    AnnotatedFormula = GetAnnotatedFormulaFromListByName(Head,"pel47_14");
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    Universals = CountAnnotatedFormulaUniqueVariablesByUse(AnnotatedFormula,
-1,-1,universal);
    Existentials = CountAnnotatedFormulaUniqueVariablesByUse(AnnotatedFormula,
-1,-1,existential);
    printf("Universals = %d Existentials = %d\n",Universals,Existentials);
    return(EXIT_SUCCESS);

//----Test parsing of strings
    ANewTerm = ParseStringTerm("hello(there,my(BIG),friend)",nontype,
Signature,0);
    printf("The term is ==");
    PrintTSTPTerm(stdout,ANewTerm,-1,0);
    printf("==\n");

//----Test getting inference status
    AnnotatedFormula = GetAnnotatedFormulaFromListByNumber(Head,10);
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    if (GetSource(AnnotatedFormula) != NULL) {
        printf("The source is %s\n",SomeString);
        if (GetInferenceInfoTerm(AnnotatedFormula,"status",SomeString) != NULL) {
            printf("The status term is %s\n",SomeString);
        } else {
            printf("No status term\n");
        }
    } else {
        printf("No source for status\n");
    }

//----Test getting by count
    printf("There are %d clauses\n",ListCount(Head,cnf_nodes));
    AnnotatedFormula = GetAnnotatedFormulaFromListByNumber(Head,20);
    GetName(AnnotatedFormula,PutNamesHere);
    printf("Got the node for clause named %s\n",PutNamesHere);
    printf("The status is %s\n",StatusToString(GetRole(AnnotatedFormula,
&SubStatus)));
    if (SubStatus != nonstatus) {
        printf("The substatus is %s\n",StatusToString(SubStatus));
    } else {
        printf("It has no substatus\n");
    }
    if (GetInferenceRule(AnnotatedFormula,SomeString) != NULL) {
        printf("The inference rule is %s\n",SomeString);
    } else {
        printf("No inference rule found\n");
    }

//----Print symbol extraction
    PrintAnnotatedTSTPNode(stdout,AnnotatedFormula,tptp,1);
    if (CountLiteralsOfPolarity(AnnotatedFormula,&Positive,&Negative)) {
        printf("The clause has %d literals, %d positive, %d negative\n",
CountAnnotatedFormulaAtomsByPredicate(AnnotatedFormula,""),Positive,Negative);
    }
    if ((Literal = GetLiteralFromAnnotatedClauseByNumber(AnnotatedFormula,1))
!= NULL) {
        printf("The literal is ");
        PrintTSTPFormula(stdout,AnnotatedFormula->Syntax,Literal,0,1,none,0);
        printf("\n");
        SymbolUsage = (char *)Malloc(sizeof(String));
        GetLiteralSymbolUsage(Literal,&SymbolUsage,&VariablesStartHere);
        printf("The literal data is \n%s\n",SymbolUsage);
        printf("The variables are \n%s\n",VariablesStartHere);

        if ((AnotherLiteral = GetLiteralFromAnnotatedClauseByNumber(
AnnotatedFormula,2)) != NULL) {
            printf("The literal is ");
            PrintTSTPFormula(stdout,AnnotatedFormula->Syntax,AnotherLiteral,
0,1,none,0);
            printf("\n");
            AnotherSymbolUsage = (char *)Malloc(sizeof(String));
            if (GetLiteralSymbolUsage(AnotherLiteral,&AnotherSymbolUsage,
NULL) != NULL) {
                printf("The literal data is \n%s\n",AnotherSymbolUsage);
            }
            ExtendString(&SymbolUsage,AnotherSymbolUsage,&SymbolUsageLength);
            NormalizeSymbolUsage(SymbolUsage);
            printf("The combined data is \n%s\n",SymbolUsage);
            Free((void **)&AnotherSymbolUsage);
        } else {
            printf("Could not get literal number 2\n");
        }
        Free((void **)&SymbolUsage);
    } else {
        printf("Could not get literal number 1\n");
    }

    FreeListOfAnnotatedFormulae(&Head);
    assert(Head == NULL);

    return(EXIT_SUCCESS);

//----Test SZS hierarchy
    for (SZS1=SZS;SZS1<nonszsresult;SZS1++) {
        printf("%s (%s,%s) %s\n",SZSResultToString(SZS1),
SZSResultToString(StringToSZSResult(SZSResultToString(SZS1))),
SZSResultToString(StringToSZSResult(SZSResultToUserString(SZS1))),
SZSResultToUserString(SZS1));
        for (SZS2=SZS1;SZS2<nonszsresult;SZS2++) {
            if (SZSIsA(SZS2,SZS1)) {
                printf("%s isa %s\n",SZSResultToString(SZS2),
SZSResultToString(SZS1));
            } else {
                printf("%s nota %s\n",SZSResultToString(SZS2),
SZSResultToString(SZS1));
            }
        }
    }
    for (SZSO1=LDa;SZSO1<nonszsoutput;SZSO1++) {
        printf("%s (%s,%s) %s\n",SZSOutputToString(SZSO1),
SZSOutputToString(StringToSZSOutput(SZSOutputToString(SZSO1))),
SZSOutputToString(StringToSZSOutput(SZSOutputToUserString(SZSO1))),
SZSOutputToUserString(SZSO1));
        for (SZSO2=SZSO1;SZSO2<nonszsoutput;SZSO2++) {
            if (SZSOutputIsA(SZSO2,SZSO1)) {
                printf("%s isa %s\n",SZSOutputToString(SZSO2),
SZSOutputToString(SZSO1));
            } else {
                printf("%s nota %s\n",SZSOutputToString(SZSO2),
SZSOutputToString(SZSO1));
            }
        }
    }
    return(EXIT_SUCCESS);

}
//-----------------------------------------------------------------------------
