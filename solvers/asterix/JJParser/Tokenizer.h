#ifndef TOKENIZER_H
#define TOKENIZER_H
//-----------------------------------------------------------------------------
#include "DataTypes.h"
//-----------------------------------------------------------------------------
#define NextCharacter(Stream) Character(Stream,1)
#define CurrentCharacter(Stream) Character(Stream,0)
#define CurrentCharacterMove(Stream) Character(Stream,-1)
#define NextToken(Stream) Token(Stream,1)
#define CurrentToken(Stream) Token(Stream,0)
#define CurrentTokenMove(Stream) Token(Stream,-1)
#define TakeCurrentToken(Stream) Token(Stream,2)
//-----------------------------------------------------------------------------
int GetNeedForNonLogicTokens(void);
void SetNeedForNonLogicTokens(int OnOff);
int GetStreamNeedForNonLogicTokens(READFILE Stream);
int GetWarnings(void);
void SetWarnings(int GiveWarnings);
int GetStreamWarnings(READFILE Stream);
int EndFile(TOKEN CurrentToken);

int Character(READFILE CurrentFile,int Operation);
ConnectiveType StringToConnective(char * String);
char * ConnectiveToString(ConnectiveType Connective);
StatusType CheckStringToStatus(char * String);
StatusType StringToStatus(char * String);
char * StatusToString(StatusType Status);
TOKEN GetNextToken(READFILE CurrentFile);
void FreeToken(TOKEN * Pointer);
TOKEN Token(READFILE CurrentFile, int Operation);
TOKEN CloneToken(TOKEN TokenCopy);
void FreeToken(TOKEN * Pointer);

void SetTokenType(READFILE Stream,TokenType Type);
int CheckTokenType(READFILE Stream,TokenType Type);
void TokenWarning(READFILE Stream,char * Message);
void TokenError(READFILE Stream);
int CheckToken(READFILE Stream,TokenType Type,char * Value);
int TakeTokenType(READFILE Stream,TokenType Type);
int TakeToken(READFILE Stream,TokenType Type,char * Value);
void EnsureTokenType(READFILE Stream,TokenType Type);
void EnsureToken(READFILE Stream,TokenType Type,char * Value);
int AcceptTokenType(READFILE Stream,TokenType Type);
int AcceptToken(READFILE Stream,TokenType Type,char * Value);
int NextThenAcceptTokenType(READFILE Stream,TokenType Type);
int NextThenAcceptToken(READFILE Stream,TokenType Type,char * Value);
//------------------------------------------------------------------------------
#endif
