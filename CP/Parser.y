{
module CP.Parser where

import Control.Monad.Error
import Control.Monad.State
import CP.Lexer
import CP.Syntax
import Data.Maybe (fromMaybe)
}

%name proc Proc
%name prop Prop
%name tops Tops
%name foterm FOTerm
%tokentype { Token }
%monad { StateT AlexState (Either String) }
%lexer { scan } { EOF }
%error { parseError }

%token
    ':'       { COLON }
    ';'       { SEMI }
    ','       { COMMA }
    '.'       { DOT }
    '/'       { SLASH }
    '('       { LPAREN }
    ')'       { RPAREN }
    '['       { LBRACK }
    ']'       { RBRACK }
    '{'       { LBRACE }
    '}'       { RBRACE }
    '|'       { BAR }
    '<->'     { LINK }
    'new'     { NEW }
    'case'    { CASE }
    'rec'     { REC }
    'corec'   { COREC }
    '?'       { QUERY }
    '!'       { BANG }

    'forall'  { FORALL }
    'exists'  { EXISTS }
    'mu'      { MU }
    'nu'      { NU }
    '*'       { TIMES }
    '||'      { PAR }
    '+'       { PLUS }
    '&'       { WITH }
    'bot'     { BOTTOM }
    '~'       { TILDE }

    '\\'      { LAMBDA }
    'bool'    { BOOL }
    'true'    { TRUE }
    'false'   { FALSE }
    'int'     { INT }
    '->'      { TO }
    'if'      { IF }
    'then'    { THEN }
    'else'    { ELSE }
    'fix'     { FIX }

    'def'     { DEF }
    'type'    { TYPE }
    '|-'      { TURNSTILE }
    '='       { EQUALS }
    'check'   { CHECK }

    '<'       { LANGLE }
    '>'       { RANGLE }

    UIdent   { UIDENT $$ }
    LIdent   { LIDENT $$ }
    IntConst { INTCONST $$ }

%%

opt(p)       : {- empty -}                    { Nothing }
             | p                              { Just $1 }

fst(p,q)     : p q                            { $1 }
snd(p,q)     : p q                            { $2 }
pair(p,q)    : p q                            { ($1, $2) }

revList(p)   : {- empty -}                    { [] }
             | revList(p) p                   { $2 : $1 }

list(p)      : revList(p)                     { reverse $1 }

sep(p,q)     : {- empty -}                    { [] }
             | sep1(p,q)                      { $1 }

sep1(p,q)    : p list(snd(q,p))               { $1 : $2 }

optSepDelim(p,q,l,r) : {- empty -}            { [] }
                                  | l sep(p,q) r                   { $2 }

labeledList(p,q) : sep(pair(p,snd(':',q)),',') { $1 }

Quant        :: { (String -> Prop -> Prop) -> (FOType -> Prop -> Prop) -> Prop }
             : UIdent '.' Prop                { \so fo -> so $1 $3 }
             | FOType '.' Prop                { \so fo -> fo $1 $3 }

Prop         :: { Prop }
             : 'exists' UIdent '.' Prop       { Exist $2 $4 }
             | 'forall' UIdent '.' Prop       { Univ $2 $4 }
             | 'mu' UIdent '.' Prop           { Mu $2 $4 }
             | 'nu' UIdent '.' Prop           { Nu $2 $4 }
             | Prop1                          { $1 }

PropOrType   :: { Prop -> (Prop -> Prop -> Prop) -> (FOType -> Prop -> Prop) -> Prop }
             : Prop                           { \b p t -> p $1 b }
             | FOType                         { \b p t -> t $1 b }

Prop1        :: { Prop }
             : PropOrType '*' Prop2           { $1 $3 Times FOExist }
             | PropOrType '||' Prop2          { $1 $3 Par FOUniv }
             | '+' '{' labeledList(LIdent, Prop) '}'
                                              { Plus $3 }
             | '&' '{' labeledList(LIdent, Prop) '}'
                                              { With $3 }
             | Prop2                          { $1 }

Prop2        :: { Prop }
             : UIdent optSepDelim(Prop, ',', '(', ')')
                                              { Var $1 $2 }
             | '~' Prop2                      { Dual $2 }
             | '!' Prop2                      { OfCourse $2 }
             | '?' Prop2                      { WhyNot $2 }
             | IntConst                       {% if $1 == 1 then return One else throwError ("Unexpected " ++ show $1) }
             | 'bot'                          { Bottom }
             | '(' Prop ')'                   { $2 }

FOType       :: { FOType }
             : FOType1 '->' FOType            { $1 `To` $3 }
             | FOType1                        { $1 }

FOType1      :: { FOType }
             : 'int'                          { Int }
             | 'bool'                         { Bool }
             | '[' Behavior ']'               { TQuote $2 }
             | '(' opt(FOType) ')'            { fromMaybe Unit $2 }

Arg          :: { Arg }
             : LIdent                         { NameArg $1 }
             | Proc                           { ProcArg $1 }

Proc         :: { Proc }
             : UIdent optSepDelim(Arg, ',', '(', ')')
                                              { ProcVar $1 $2 }
             | LIdent '<->' LIdent            { Link $1 $3 }
             | 'new' '[' LIdent ':' Prop ']' '(' Proc '|' Proc ')'
                                              { Cut $3 $5 $8 $10 }
             | LIdent '[' LIdent ']' '.' '(' Proc '|' Proc ')'
                                              { Out $1 $3 $7 $9 }
             | LIdent '(' LIdent ')' '.' Proc { In $1 $3 $6 }
             | LIdent '/' LIdent '.' Proc     { Select $1 $3 $5 }
             | 'case' LIdent '{' sep(pair(LIdent, snd(':', Proc)), ';') '}'
                                              { Case $2 $4 }
             | 'rec' LIdent '.' Proc          { Rec $2 $4 }
             | 'corec' LIdent '[' LIdent ':' Prop ']' '(' Proc ',' Proc ')'
                                              { CoRec $2 $4 $6 $9 $11 }
             | LIdent '[' Prop ']' '.' Proc   { SendProp $1 $3 $6 }
             | LIdent '(' UIdent ')' '.' Proc { ReceiveProp $1 $3 $6 }
             | LIdent '*' '[' FOTerm ']' '.' Proc
                                              { SendTerm $1 $4 $7 }
             | LIdent '*' '(' LIdent ')' '.' Proc
                                              { ReceiveTerm $1 $4 $7 }
             | LIdent '(' ')' '.' Proc        { EmptyIn $1 $5 }
             | LIdent '[' ']' '.' IntConst    {% if $5 == 0 then return (EmptyOut $1) else throwError ("Unexpected " ++ show $5) }
             | 'case' LIdent '(' sep(LIdent, ',') ')' '{' '}'
                                              { EmptyCase $2 $4 }
             | '!' LIdent '(' LIdent ')' '.' Proc
                                              { Replicate $2 $4 $7 }
             | '[' FOTerm ']'                 { Quote $2 Nothing }
             | '?' LIdent '[' LIdent ']' '.' Proc
                                              { Derelict $2 $4 $7 }
             | '?' optSepDelim(LIdent, ',', '(', ')')
                                              { Unk $2 }

FOTerm       :: { FOTerm }
             : '\\' LIdent ':' FOType '.' FOTerm
                                              { ELam $2 $4 $6 }
             | 'if' FOTerm 'then' FOTerm 'else' FOTerm
                                              { EIf $2 $4 $6 }
             | FOApp                          { $1 }

FOApp        :: { FOTerm }
             : FOApp1 '+' FOApp               { EApp (EApp (EVar "+") $1) $3 }
             | FOApp1                         { $1 }

FOApp1       :: { FOTerm }
             : FOApp2 '*' FOApp1              { EApp (EApp (EVar "*") $1) $3 }
             | FOApp2                         { $1 }

FOApp2       :: { FOTerm }
             : FOApp2 FOAtom                  { EApp $1 $2 }
             | 'fix' FOAtom                   { EFix $2 }
             | FOAtom                         { $1 }

FOAtom       :: { FOTerm }
             : 'true'                         { EBool True }
             | 'false'                        { EBool False }
             | LIdent                         { EVar $1 }
             | IntConst                       { EInt $1 }
             | '[' Proc '|-' Behavior ']'     { EQuote $2 $4 }
             | '(' opt(FOTerm) ')'            { fromMaybe EUnit $2 }

Param        :: { Param }
             : LIdent                         { NameParam $1 }
             | UIdent                         { ProcParam $1 }

Defn         :: { Defn }
             : 'def' UIdent optSepDelim(Param, ',', '(', ')') '=' Proc '.'
                                              { ProcDef $2 $3 $5 }
             | 'type' UIdent optSepDelim(UIdent, ',', '(', ')') '=' Prop '.'
                                              { PropDef $2 $3 $5 }

Behavior     :: { Behavior }
             : sep1(pair(LIdent,snd(':', Prop)),',')
                                              { $1 }

Assertion    :: { Assertion }
             : 'check' Assertion1             { $2 True }
             | Assertion1                     { $1 False }

Assertion1   :: { Bool -> Assertion }
             : Proc '|-' Behavior '.'         { Assert $1 $3 }

Top          :: { Either Defn Assertion}
             : Defn                           { Left $1 }
             | Assertion                      { Right $1 }

Tops         :: { [Either Defn Assertion] }
             : list(Top)                      { $1 }

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
