#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include "Tokenizer.h"
#include "Signature.h"
#include "Utilities.h"
#include "DataTypes.h"
//-----------------------------------------------------------------------------
SYMBOLNODE NewSignatureNode(char * Name,int Arity) {

    SYMBOLNODE Symbol;

    Symbol = (SYMBOLNODE)Malloc(sizeof(SymbolNodeType));
    Symbol->NameSymbol = CopyHeapString(Name);
    Symbol->NumberOfUses = 1;
    Symbol->Arity = Arity;
    Symbol->LastSymbol = NULL;
    Symbol->NextSymbol = NULL;

    return(Symbol);
}
//-----------------------------------------------------------------------------
SIGNATURE NewSignature(void) {

    SIGNATURE Signature;

    Signature = (SIGNATURE)Malloc(sizeof(SignatureType));
    Signature->Variables = NULL;
    Signature->Functions = NULL;
    Signature->Predicates = NULL;
    Signature->NonLogicals = NULL;

    return(Signature);
}
//-----------------------------------------------------------------------------
SYMBOLNODE DuplicateSymbols(SYMBOLNODE Original) {

    SYMBOLNODE Copy;

    if (Original == NULL) {
        Copy = NULL;
    } else {
        Copy = NewSignatureNode(Original->NameSymbol,Original->Arity);
        Copy->NumberOfUses = Original->NumberOfUses;
        Copy->LastSymbol = DuplicateSymbols(Original->LastSymbol);
        Copy->NextSymbol = DuplicateSymbols(Original->NextSymbol);
    }

    return(Copy);
}
//-----------------------------------------------------------------------------
SIGNATURE DuplicateSignature(SIGNATURE Original) {

    SIGNATURE Copy;

    Copy = NewSignature();
    Copy->Variables = DuplicateSymbols(Original->Variables);
    Copy->Functions = DuplicateSymbols(Original->Functions);
    Copy->Predicates = DuplicateSymbols(Original->Predicates);
    Copy->NonLogicals = DuplicateSymbols(Original->NonLogicals);

    return(Copy);
}
//-----------------------------------------------------------------------------
void FreeSignatureList(SYMBOLNODE * Symbols) {

    if ((*Symbols) != NULL) {
        assert((*Symbols)->NumberOfUses == 0);
        FreeSignatureList(&((*Symbols)->LastSymbol));
        FreeSignatureList(&((*Symbols)->NextSymbol));
        Free((void **)(&((*Symbols)->NameSymbol)));
        Free((void **)Symbols);
    }
}
//-----------------------------------------------------------------------------
void FreeSignature(SIGNATURE * Signature) {

    FreeSignatureList(&((*Signature)->Variables));
    assert((*Signature)->Variables == NULL);
    FreeSignatureList(&((*Signature)->Functions));
    assert((*Signature)->Functions == NULL);
    FreeSignatureList(&((*Signature)->Predicates));
    assert((*Signature)->Predicates == NULL);
    FreeSignatureList(&((*Signature)->NonLogicals));
    assert((*Signature)->NonLogicals == NULL);

    Free((void **)Signature);
}
//-----------------------------------------------------------------------------
SYMBOLNODE RemoveSignatureNodeFromTree(SYMBOLNODE * OneToDeletePtr) {

    SYMBOLNODE * LargestPointer;
    SYMBOLNODE Deleted;

    Deleted = *OneToDeletePtr;

    if (Deleted->LastSymbol == NULL) {
        if (Deleted->NextSymbol != NULL) {
            *OneToDeletePtr = Deleted->NextSymbol;
        } else {
            *OneToDeletePtr = NULL;
        }
    } else if (Deleted->NextSymbol == NULL) {
        *OneToDeletePtr = Deleted->LastSymbol;
    } else {
        LargestPointer = &(Deleted->LastSymbol);
        while ((*LargestPointer)->NextSymbol != NULL) {
            LargestPointer = &((*LargestPointer)->NextSymbol);
        }
        *OneToDeletePtr = RemoveSignatureNodeFromTree(LargestPointer);
        (*OneToDeletePtr)->LastSymbol = Deleted->LastSymbol;
        (*OneToDeletePtr)->NextSymbol = Deleted->NextSymbol;
    }
    return(Deleted);
}
//-----------------------------------------------------------------------------
int RemovedUnusedSymbolsFromList(SYMBOLNODE * Symbols) {

    int NumberRemoved;
    SYMBOLNODE ToFree;

    NumberRemoved = 0;
    if (*Symbols != NULL) {
        NumberRemoved += RemovedUnusedSymbolsFromList(&((*Symbols)->
LastSymbol));
        NumberRemoved += RemovedUnusedSymbolsFromList(&((*Symbols)->
NextSymbol));
        if ((*Symbols)->NumberOfUses  == 0) {
            ToFree = RemoveSignatureNodeFromTree(Symbols);
            Free((void **)&ToFree);
            NumberRemoved++;
        }
    }

    return(NumberRemoved);
}
//-----------------------------------------------------------------------------
int RemovedUnusedSymbols(SIGNATURE Signature) {

    int TotalRemoved;

    TotalRemoved = 0;
    TotalRemoved += RemovedUnusedSymbolsFromList(&(Signature->Variables));
    TotalRemoved += RemovedUnusedSymbolsFromList(&(Signature->Functions));
    TotalRemoved += RemovedUnusedSymbolsFromList(&(Signature->Predicates));
    TotalRemoved += RemovedUnusedSymbolsFromList(&(Signature->NonLogicals));

    return(TotalRemoved);
}
//-----------------------------------------------------------------------------
char * GetSignatureSymbol(SYMBOLNODE SymbolNode) {

    return(SymbolNode->NameSymbol);
}
//-----------------------------------------------------------------------------
int GetSignatureArity(SYMBOLNODE SymbolNode) {

    return(SymbolNode->Arity);
}
//-----------------------------------------------------------------------------
int GetSignatureUses(SYMBOLNODE SymbolNode) {

    return(SymbolNode->NumberOfUses);
}
//-----------------------------------------------------------------------------
void IncreaseSymbolUseCount(SYMBOLNODE Symbol,int HowMuch) {

    Symbol->NumberOfUses += HowMuch;
}
//-----------------------------------------------------------------------------
SYMBOLNODE IsSymbolInSignatureList(SYMBOLNODE List,char * Name,int Arity) {

    if (List == NULL || (!strcmp(GetSignatureSymbol(List),Name) &&
GetSignatureArity(List) == Arity)) {
        return(List);
    } else if (strcmp(Name,GetSignatureSymbol(List)) < 0 ||
(strcmp(Name,GetSignatureSymbol(List)) == 0 && 
 Arity < GetSignatureArity(List))) {
        return(IsSymbolInSignatureList(List->LastSymbol,Name,Arity));
    } else {
        return(IsSymbolInSignatureList(List->NextSymbol,Name,Arity));
    }
}
//-----------------------------------------------------------------------------
SYMBOLNODE InsertIntoSignatureList(SYMBOLNODE * List,char * Name,int Arity,
READFILE Stream) {

    SuperString DuplicateArity;

    if (*List == NULL) {
        *List = NewSignatureNode(Name,Arity);
        return(*List);
    } 

//----Same name
    if (!strcmp(GetSignatureSymbol(*List),Name)) {
//----Same arity, we're done
        if (GetSignatureArity(*List) == Arity) {
            IncreaseSymbolUseCount(*List,1);
            return(*List);
        } else {
            if (Stream != NULL && GetStreamWarnings(Stream)) {
//----Warning if symbol overloading is not allowed
                sprintf(DuplicateArity,
"Multiple arity symbol %s, arity %d and now %d",
Name,GetSignatureArity(*List),Arity);
                TokenWarning(Stream,DuplicateArity);
            } 
        }
    }

    if (strcmp(Name,GetSignatureSymbol(*List)) < 0 ||
(strcmp(Name,GetSignatureSymbol(*List)) == 0 && 
 Arity < GetSignatureArity(*List))) {
        return(InsertIntoSignatureList(&((*List)->LastSymbol),Name,Arity,
Stream));
    } else {
        return(InsertIntoSignatureList(&((*List)->NextSymbol),Name,Arity,
Stream));
    }
}
//-----------------------------------------------------------------------------
SYMBOLNODE InsertIntoSignature(SIGNATURE Signature,TermType Type,
char * Name,int Arity,READFILE Stream) {

//DEBUG printf("%s %d ==%d\n",Name,Arity,Type);
    switch (Type) {
        case variable:
            return(InsertIntoSignatureList(&(Signature->Variables),Name,Arity,
Stream));
            break;
        case function:
            return(InsertIntoSignatureList(&(Signature->Functions),Name,Arity,
Stream));
            break;
        case predicate:
            return(InsertIntoSignatureList(&(Signature->Predicates),Name,
Arity,Stream));
            break;
        case non_logical_data:
            return(InsertIntoSignatureList(&(Signature->NonLogicals),Name,
Arity,Stream));
            break;
        default:
            printf("ERROR: Unknown type for signature, %s %d\n",Name,Arity);
            exit(EXIT_FAILURE);
    }
}
//-----------------------------------------------------------------------------
void DoNextInSignature(SYMBOLNODE SignatureTree,SYMBOLNODE Current,
int * CurrentFound,int * NextFound,SYMBOLNODE * Next) {

//----If the tree exists and the next (after current) has not been found
    if (SignatureTree != NULL && !*NextFound) {
//----If the current has not even been found, search on
        if (!*CurrentFound) {
//----If there's a current one (not the first time) and this is it, woohoo
            if (Current != NULL && 
!strcmp(GetSignatureSymbol(SignatureTree),GetSignatureSymbol(Current)) && 
GetSignatureArity(SignatureTree) == GetSignatureArity(Current)) {
//----If there's a right subtree, get the left most of that
                if (SignatureTree->NextSymbol != NULL) {
                    DoNextInSignature(SignatureTree->NextSymbol,NULL,
CurrentFound,NextFound,Next);
//----Otherwise catch the next on the way out of the recursion
                } else {
                    *CurrentFound = 1;
                }
//----If there's no current one (first time) or the current is small, go left
            } else if (Current == NULL || 
strcmp(GetSignatureSymbol(Current),GetSignatureSymbol(SignatureTree)) < 0 ||
(strcmp(GetSignatureSymbol(Current),GetSignatureSymbol(SignatureTree)) == 0 &&
 GetSignatureArity(Current) < GetSignatureArity(SignatureTree))) {
                DoNextInSignature(SignatureTree->LastSymbol,Current,
CurrentFound,NextFound,Next);
//----If current found to the (immediate ... next not found) left, catch 
//----the next one here
                if (*CurrentFound && !*NextFound) {
                    *NextFound = 1;
                    *Next = SignatureTree;
                }
//----Current exists and is larger ... head right
            } else {
                DoNextInSignature(SignatureTree->NextSymbol,Current,
CurrentFound,NextFound,Next);
            }
//----If the current has been found, then we're one level on the way out
//----of the recursion, and this is the next. Catch it.
        } else {
            *Next = SignatureTree;
            *NextFound = 1;
        }
//----If at the end of the tree, then the current does not exist, i.e., must
//----have been NULL, so we've reached the left corner. Mark current as found
//----so left corner node is caught on way out of recursion.
    } else {
        *CurrentFound = 1;
    }
}
//-----------------------------------------------------------------------------
SYMBOLNODE NextInSignatureTree(SYMBOLNODE SignatureTree,SYMBOLNODE Current) {

    SYMBOLNODE Next;
    int CurrentFound;
    int NextFound;

    Next = NULL;
    CurrentFound = 0;
    NextFound = 0;
    DoNextInSignature(SignatureTree,Current,&CurrentFound,&NextFound,&Next);
    return(Next);
}
//-----------------------------------------------------------------------------
void ListSignatureBySearch(SYMBOLNODE SignatureTree) {

    SYMBOLNODE Current;

    Current = NextInSignatureTree(SignatureTree,NULL);
    while (Current != NULL) {
        printf("%s/%d(%d)\n",GetSignatureSymbol(Current),
GetSignatureArity(Current),GetSignatureUses(Current));
        fflush(stdout);
        Current = NextInSignatureTree(SignatureTree,Current);
    }
}
//-----------------------------------------------------------------------------
void PrintSignatureTree(SYMBOLNODE SignatureTree) {

    if (SignatureTree != NULL) {
        PrintSignatureTree(SignatureTree->LastSymbol);
        printf("%s/%d(%d)\n",GetSignatureSymbol(SignatureTree),
GetSignatureArity(SignatureTree),GetSignatureUses(SignatureTree));
        fflush(stdout);
        PrintSignatureTree(SignatureTree->NextSymbol);
    }
}
//-----------------------------------------------------------------------------
void PrintSignature(SIGNATURE Signature) {

    printf("Variables:  ");
    PrintSignatureTree(Signature->Variables);
    printf("\n");
    printf("Functions:  ");
    PrintSignatureTree(Signature->Functions);
    printf("\n");
    printf("Predicates: ");
    PrintSignatureTree(Signature->Predicates);
    printf("\n");
    printf("NonLogical: ");
    PrintSignatureTree(Signature->NonLogicals);
    printf("\n");
}
//-----------------------------------------------------------------------------
void DoGetSignatureSymbolUsage(char ** PutUsageHere,char ** PutNextHere,
SYMBOLNODE Current,long * UsageLength,int * SpareLength) {

//DEBUG static long Counter = 0;

    if (Current != NULL) {
        DoGetSignatureSymbolUsage(PutUsageHere,PutNextHere,Current->LastSymbol,
UsageLength,SpareLength);
//----Get more memory if not lots spare
        if (*SpareLength < SUPERSTRINGLENGTH) {
//DEBUG printf("Need to ask for %ld memory\n",*UsageLength+SUPERSTRINGLENGTH);
            *PutUsageHere = (char *)Realloc((void *)*PutUsageHere,
*UsageLength+SUPERSTRINGLENGTH);
            *SpareLength += SUPERSTRINGLENGTH;
            *UsageLength += SUPERSTRINGLENGTH;
        }
//DEBUG printf("About to print %s into %d spare\n",Current->NameSymbol,*SpareLength);
//---Avoid using API to get max speed
        sprintf(*PutNextHere,"%s/%d/%d\n",Current->NameSymbol,Current->Arity,
Current->NumberOfUses);
        *SpareLength -= strlen(*PutNextHere);
//DEBUG printf("Printed %s leaving %d\n",*PutNextHere,*SpareLength);
        *PutNextHere += strlen(*PutNextHere);
//DEBUG if (++Counter % 1000 == 0) printf("%ld\n",Counter);

        DoGetSignatureSymbolUsage(PutUsageHere,PutNextHere,Current->NextSymbol,
UsageLength,SpareLength);
    }
}
//-----------------------------------------------------------------------------
//----PutUsageHere must be address of a malloced String
char * GetSignatureSymbolUsage(SIGNATURE Signature,char ** PutUsageHere,
char ** FunctorUsageStartsHere) {

    int SpareLength;
    long UsageLength;
    char * PutNextHere;

    strcpy(*PutUsageHere,"");
    UsageLength = STRINGLENGTH;
    SpareLength = STRINGLENGTH;
    PutNextHere = *PutUsageHere;
    DoGetSignatureSymbolUsage(PutUsageHere,&PutNextHere,Signature->Predicates,
&UsageLength,&SpareLength);
    *FunctorUsageStartsHere = PutNextHere;
    DoGetSignatureSymbolUsage(PutUsageHere,&PutNextHere,Signature->Functions,
&UsageLength,&SpareLength);
//DEBUG printf("===\n%s",*PutUsageHere);
    return(*PutUsageHere);
}
//-----------------------------------------------------------------------------
void DoGetSignatureSymbolUsageStatistics(SYMBOLNODE SignatureNode,
double * NumberOfSymbols,double * NumberOfSymbolsArity0,
double * MinSymbolArity,double * MaxSymbolArity) {

    if (SignatureNode != NULL) {
//DEBUG printf("Symbol is %s\n",SignatureNode->NameSymbol);
        (*NumberOfSymbols)++;
        if (SignatureNode->Arity == 0) {
            (*NumberOfSymbolsArity0)++;
        }
        if (*MinSymbolArity == -1 || SignatureNode->Arity < *MinSymbolArity) {
            *MinSymbolArity = SignatureNode->Arity;
        }
        if (SignatureNode->Arity > *MaxSymbolArity) {
            *MaxSymbolArity = SignatureNode->Arity;
        }
        DoGetSignatureSymbolUsageStatistics(SignatureNode->LastSymbol,
NumberOfSymbols,NumberOfSymbolsArity0,MinSymbolArity,MaxSymbolArity);
        DoGetSignatureSymbolUsageStatistics(SignatureNode->NextSymbol,
NumberOfSymbols,NumberOfSymbolsArity0,MinSymbolArity,MaxSymbolArity);
    }
}
//-----------------------------------------------------------------------------
void GetSignatureSymbolUsageStatistics(SYMBOLNODE SignatureNode,
double * NumberOfSymbols,double * NumberOfSymbolsArity0,
double * MinSymbolArity,double * MaxSymbolArity) {

    *NumberOfSymbols = 0;
    *NumberOfSymbolsArity0 = 0;
    *MinSymbolArity = -1;
    *MaxSymbolArity = -1;
    DoGetSignatureSymbolUsageStatistics(SignatureNode,NumberOfSymbols,
NumberOfSymbolsArity0,MinSymbolArity,MaxSymbolArity);
}
//-----------------------------------------------------------------------------
