#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <ctype.h>
#include <stdlib.h>
#include "DataTypes.h"
#include "Utilities.h"
#include "Signature.h"
#include "Parsing.h"
#include "PrintTSTP.h"
#include "Examine.h"
#include "Compare.h"
//-----------------------------------------------------------------------------
int SameTerm(TERM Term1,TERM Term2,int AllowVariableRenaming,
int AllowCommutation,VARIABLERENAMING * RenamedVariables);
int DoSameFormula(FORMULA Formula1,FORMULA Formula2,int AllowVariableRenaming,
int AllowCommutation,VARIABLERENAMING * RenamedVariables);
//-----------------------------------------------------------------------------
int SameVariables(VARIABLENODE Variable1,VARIABLENODE Variable2,
int AllowVariableRenaming,VARIABLERENAMING * RenamedVariables) {

    VARIABLERENAMING RenamingNode;
    int SameVariableModuloRenaming;

    if (AllowVariableRenaming) {
//----Search through the renaming nodes for the orginal
        RenamingNode = *RenamedVariables;
        while (RenamingNode != NULL && RenamingNode->OriginalVariable !=
Variable1) {
            RenamingNode = RenamingNode->NextVariableRenaming;
        }
//----No renaming node yet, so make one
        if (RenamingNode == NULL) {
            RenamingNode = (VARIABLERENAMING)
Malloc(sizeof(VariableRenamingNode));
            RenamingNode->OriginalVariable = Variable1;
            RenamingNode->RenamedVariable = Variable2;
            RenamingNode->NextVariableRenaming = *RenamedVariables;
            *RenamedVariables = RenamingNode;
            return(1);
        } else {
            return(RenamingNode->RenamedVariable == Variable2);
        }
    } else {
//----Otherwise they must point to the same node in the signature
        SameVariableModuloRenaming = 
Variable1->VariableName == Variable2->VariableName;
    }

    return(SameVariableModuloRenaming &&
SameTerm(Variable1->Instantiation,Variable2->Instantiation,
AllowVariableRenaming,0,RenamedVariables));

}
//-----------------------------------------------------------------------------
int SameArguments(TERM Arguments1[],TERM Arguments2[],int Arity,
int AllowVariableRenaming,VARIABLERENAMING * RenamedVariables) {

    int Index;

    for (Index = 0; Index < Arity; Index++) {
        if (!SameTerm(Arguments1[Index],Arguments2[Index],
AllowVariableRenaming,0,RenamedVariables)) {
            return(0);
        }
    }
    return(1);
}
//-----------------------------------------------------------------------------
int SameTerm(TERM Term1,TERM Term2,int AllowVariableRenaming,
int AllowCommutation,VARIABLERENAMING * RenamedVariables) {

    TERM TermSwapper;
    int SameModuloCommutation;

    if (Term1 == NULL || Term2 == NULL) {
        return(Term1 == Term2);
    }

    if (Term1->Type != Term2->Type || 
Term1->FlexibleArity != Term2->FlexibleArity) {
        return(0);
    }

    switch (Term1->Type) {
        case predicate:
//----If equality then compare modulo allowing commutation, else fall
//----through to term case.
            if (Term1->TheSymbol.NonVariable == Term2->TheSymbol.NonVariable &&
!strcmp(GetSymbol(Term1),"=")) {
                if (SameArguments(Term1->Arguments,Term2->Arguments,
Term1->TheSymbol.NonVariable->Arity,AllowVariableRenaming,RenamedVariables)) {
                    return(1);
                } else if (AllowCommutation) {
                    TermSwapper = Term1->Arguments[0];
                    Term1->Arguments[0] = Term1->Arguments[1];
                    Term1->Arguments[1] = TermSwapper;
                    SameModuloCommutation = SameArguments(Term1->Arguments,
Term2->Arguments,Term1->TheSymbol.NonVariable->Arity,AllowVariableRenaming,
RenamedVariables);
                    TermSwapper = Term1->Arguments[0];
                    Term1->Arguments[0] = Term1->Arguments[1];
                    Term1->Arguments[1] = TermSwapper;
                    return(SameModuloCommutation);
                } else {
                    return(0);
                }
            }
        case function:
            return(
//----Checking the symbols' nodes automatically checks the arity
Term1->TheSymbol.NonVariable == Term2->TheSymbol.NonVariable &&
SameArguments(Term1->Arguments,Term2->Arguments,Term1->TheSymbol.NonVariable->
Arity,AllowVariableRenaming,RenamedVariables));
            break;
        case variable:
            return(SameVariables(Term1->TheSymbol.Variable,
Term2->TheSymbol.Variable,AllowVariableRenaming,RenamedVariables));
            break;
        default:
            printf("ERROR: Not a formula type for comparison\n");
            exit(EXIT_FAILURE);
            break;
    }
}
//-----------------------------------------------------------------------------
int SameQuantifiedFormula(QuantifiedFormulaType Formula1,QuantifiedFormulaType 
Formula2,int AllowVariableRenaming,int AllowCommutation,
VARIABLERENAMING * RenamedVariables) {

    return(Formula1.Quantifier == Formula2.Quantifier &&
Formula1.ExistentialCount == Formula2.ExistentialCount &&
SameTerm(Formula1.Variable,Formula2.Variable,AllowVariableRenaming,0,
RenamedVariables) &&
DoSameFormula(Formula1.Formula,Formula2.Formula,AllowVariableRenaming,
AllowCommutation,RenamedVariables));
}
//-----------------------------------------------------------------------------
int SameBinaryFormula(BinaryFormulaType Formula1,BinaryFormulaType Formula2,
int AllowVariableRenaming,int AllowCommutation,
VARIABLERENAMING * RenamedVariables) {

    return(Formula1.Connective == Formula2.Connective &&
DoSameFormula(Formula1.LHS,Formula2.LHS,AllowVariableRenaming,
AllowCommutation,RenamedVariables) &&
DoSameFormula(Formula1.RHS,Formula2.RHS,AllowVariableRenaming,
AllowCommutation,RenamedVariables));
}
//-----------------------------------------------------------------------------
int SameUnaryFormula(UnaryFormulaType Formula1,UnaryFormulaType Formula2,
int AllowVariableRenaming,int AllowCommutation,
VARIABLERENAMING * RenamedVariables) {

    return(Formula1.Connective == Formula2.Connective &&
DoSameFormula(Formula1.Formula,Formula2.Formula,AllowVariableRenaming,
AllowCommutation,RenamedVariables));
}
//-----------------------------------------------------------------------------
int DoSameFormula(FORMULA Formula1,FORMULA Formula2,int AllowVariableRenaming,
int AllowCommutation,VARIABLERENAMING * RenamedVariables) {

    if (Formula1 == NULL || Formula2 == NULL) {
        return(Formula1 == Formula2);
    }

    if (Formula1->Type != Formula2->Type) {
        return(0);
    }

    switch (Formula1->Type) {
        case quantified:
            return(SameQuantifiedFormula(Formula1->
FormulaUnion.QuantifiedFormula,Formula2->FormulaUnion.QuantifiedFormula,
AllowVariableRenaming,AllowCommutation,RenamedVariables));
            break;
        case binary:
            return(SameBinaryFormula(Formula1->FormulaUnion.BinaryFormula,
Formula2->FormulaUnion.BinaryFormula,AllowVariableRenaming,AllowCommutation,
RenamedVariables));
            break;
        case unary:
            return(SameUnaryFormula(Formula1->FormulaUnion.UnaryFormula,
Formula2->FormulaUnion.UnaryFormula,AllowVariableRenaming,AllowCommutation,
RenamedVariables));
            break;
        case atom:
            return(SameTerm(Formula1->FormulaUnion.Atom,Formula2->
FormulaUnion.Atom,AllowVariableRenaming,AllowCommutation,RenamedVariables));
            break;
        default:
            printf("ERROR: Not a formula type for comparison\n");
            exit(EXIT_FAILURE);
            break;
    }

}
//-----------------------------------------------------------------------------
int SameFormula(FORMULA Formula1,FORMULA Formula2,int AllowVariableRenaming,
int AllowCommutation) {

    VARIABLERENAMING RenamedVariables;
    VARIABLERENAMING NextNode;
    int Result;

    RenamedVariables = NULL;
    Result = DoSameFormula(Formula1,Formula2,AllowVariableRenaming,
AllowCommutation,&RenamedVariables);

//----Free renamed variable list
    while (RenamedVariables != NULL) {
        NextNode = RenamedVariables->NextVariableRenaming;
        Free((void **)&RenamedVariables);
        RenamedVariables = NextNode;
    }

    return(Result);
}
//-----------------------------------------------------------------------------
int SameFormulaInAnnotatedFormulae(ANNOTATEDFORMULA AnnotatedFormula1,
ANNOTATEDFORMULA AnnotatedFormula2,int AllowVariableRenaming,
int AllowCommutation) {

    if (LogicalAnnotatedFormula(AnnotatedFormula1)) {
        return(CheckAnnotatedFormula(AnnotatedFormula2,
AnnotatedFormula1->Syntax) &&
SameFormula(AnnotatedFormula1->AnnotatedFormulaUnion.AnnotatedTSTPFormula.
FormulaWithVariables->Formula,AnnotatedFormula2->AnnotatedFormulaUnion.
AnnotatedTSTPFormula.FormulaWithVariables->Formula,AllowVariableRenaming,
AllowCommutation));
    } else {
        return(0);
    }
}
//-----------------------------------------------------------------------------
//int SameFormulaInAnnotatedFormulaString(ANNOTATEDFORMULA AnnotatedFormula,
//char * AnnotatedFormulaString,int AllowVariableRenaming) {
//
//    LISTNODE Head2;
//    SIGNATURE Signature;
//    int Same;
//
//----Need to pass in the Signature because test uses signature nodes AAAARGH
//    if ((Head2 = ParseStringOfFormulae(AnnotatedFormulaString,Signature,0,
//NULL)) != NULL) {
//        Same = SameFormulaInAnnotatedFormulae(AnnotatedFormula,
//Head2->AnnotatedFormula,AllowVariableRenaming);
//        FreeListOfAnnotatedFormulae(&Head2);
//    } else {
//        return(0);
//    }
//}
//-----------------------------------------------------------------------------
