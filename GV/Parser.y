{
module GV.Parser where

import Control.Monad.Error
import Control.Monad.State
import GV.Lexer
import GV.Syntax
}

%name prog Prog
%name typ Type
%tokentype { Token }
%monad { StateT AlexState (Either String) }
%lexer { scan } { EOF }
%error { parseError }


%token
     ':'          { COLON }
     ';'          { SEMI }
     ','          { COMMA }
     '.'          { DOT }
     '=>'         { RIGHTARROW }
     '('          { LPAREN }
     ')'          { RPAREN }
     '['          { LBRACK }
     ']'          { RBRACK }
     '{'          { LBRACE }
     '}'          { RBRACE }
     'link'       { LINK }
     '\\'         { LAMBDA }
     'let'        { LET }
     'in'         { IN }
     'send'       { SEND }
     'receive'    { RECEIVE }
     'select'     { SELECT }
     'case'       { CASE }
     'of'         { OF }
     'terminate'  { TERMINATE }
     'serve'      { SERVE }
     'request'    { REQUEST }
     'sendType'   { SENDTYPE }
     'receiveType' { RECEIVETYPE }
     'fork'       { FORK }
     'unit'       { UNIT }

     '?'          { QUERY }
     '!'          { BANG }
     '*'          { TIMES }
     '+'          { PLUS }
     '&'          { AMP }
     '~'          { TILDE }
     '%'          { SERVER }
     '#'          { SERVICE }
     'end!'       { OUTTERM }
     'end?'       { INTERM}
     '-@'         { LINFUN }
     '->'         { UNLFUN }
     'Unit'       { UNITTYPE }

     'int'        { INT }

     '|-'         { TURNSTILE }
     '='          { EQUALS }

     UIdent       { UIDENT $$ }
     LIdent       { LIDENT $$ }
     IntConst     { INTCONST $$ }



%%

fst(p,q)     : p q                            { $1 }
snd(p,q)     : p q                            { $2 }
pair(p,q)    : p q                            { ($1, $2) }
triple(p,q,r) : p q r                         { ($1, $2, $3) }

revList(p)   : {- empty -}                    { [] }
             | revList(p) p                   { $2 : $1 }

list(p)      : revList(p)                     { reverse $1 }

sep(p,q)     : {- empty -}                    { [] }
             | sep1(p,q)                      { $1 }

sep1(p,q)    : p list(snd(q,p))               { $1 : $2 }

optSepDelim(p,q,l,r) : {- empty -}            { [] }
             | l sep(p,q) r                   { $2 }

labeledList(p,q) : sep(pair(p,snd(':',q)),',') { $1 }

Session      :: { Session }
             : '!' Type '.' Session           { Output $2 $4 }
             | '?' Type '.' Session           { Input $2 $4 }
             | '+' '{' labeledList(LIdent, Session) '}'
                                              { Sum $3 }
             | '&' '{' labeledList(LIdent, Session) '}'
                                              { Choice $3 }
             | 'end!'                         { OutTerm }
             | 'end?'                         { InTerm }
             | '%' Session                    { Server $2 }
             | '#' Session                    { Service $2 }
             | '~' Session                    { dual $2 }
             | UIdent                         { SVar $1 }
             | '!' '[' UIdent ']' '.' Session { OutputType $3 $6 }
             | '?' '[' UIdent ']' '.' Session { InputType $3 $6 }

Type        :: { Type }
            : Type1 '-@' Type                 { LinFun $1 $3 }
            | Type1 '->' Type                 { UnlFun $1 $3 }
            | 'Unit'                          { UnitType }
            | 'int'                           { Int }
            | Type1                           { $1 }

Type1       :: { Type }
            : Type2 '*' Type1                 { Tensor $1 $3 }
            | Type2                           { $1 }

Type2       :: { Type }
            : Session                         { Lift $1 }
            | '(' Type ')'                    { $2 }

Pattern     :: { Pattern }
            : LIdent                          { BindName $1 }
            | '(' LIdent ',' LIdent ')'       { BindPair $2 $4 }

Term        :: { Term }
            : 'link' Term1 Term1              { Link $2 $3 }
            | '\\' LIdent ':' Type '=>' Term  { LinLam $2 $4 $6 }
            | '!' '\\' LIdent ':' Type '=>' Term
                                              { UnlLam $3 $5 $7 }
            | Term Term1                      { App $1 $2 }
            | 'let' Pattern '=' Term 'in' Term { Let $2 $4 $6 }
            | 'send' Term1 Term               { Send $2 $3 }
            | 'receive' Term1                 { Receive $2 }
            | 'select' LIdent Term            { Select $2 $3 }
            | 'case' Term 'of' '{' sep(triple(LIdent, fst(LIdent, '=>'), Term), ';') '}'
                                              { Case $2 $5 }
            | 'case' Term '(' sep(LIdent, ',') ')' ':' Type '{' '}'
                                              { EmptyCase $2 $4 $7 }
            | 'fork' LIdent ':' Session '=>' Term
                                              { Fork $2 $4 $6 }
            | 'serve' LIdent ':' Session '=>' Term
                                              { Serve $2 $4 $6 }
            | 'request' Term                  { Request $2 }
            | 'sendType' Session Term         { SendType $2 $3 }
            | 'receiveType' Term              { ReceiveType $2 }
            | 'unit'                          { Unit }
            | Term1                           { $1 }

Term1       :: { Term }
            : LIdent                          { Var $1 }
            | IntConst                        { EInt $1 }
            | '(' Term ',' Term ')'           { Pair $2 $4 }
            | '(' Term ')'                    { $2 }

Assertion   :: { Assertion }
            : labeledList(LIdent, Type) '|-' Term ':' Type
                                              { Assert $1 $3 $5 }

Prog        :: { [Assertion] }
            : list(fst(Assertion, '.'))       { $1 }


{

parseError _ = do AlexPn _ line col <- gets alex_pos
                  throwError ("Parse error at line " ++ show line ++ ", column " ++ show col)


scan cont = do s <- get
               case unAlex alexMonadScan s of
                 Left err -> let AlexPn _ line col = alex_pos s
                             in  throwError ("Lexer error at line " ++ show line ++ ", column " ++ show col)
                 Right (s', t) -> put s' >> cont t

lexInit s = AlexState { alex_pos = alexStartPos,
                        alex_inp = s,
                        alex_chr = '\n',
                        alex_bytes = [],
                        alex_scd = 0 }

parse p s = evalStateT p (lexInit s)

}
