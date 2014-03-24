{
module GV.Lexer where
}

%wrapper "monad"

$upper  = A-Z
$lower  = a-z
$digit  = 0-9
$any    = [$upper $lower $digit _]

@uident = $upper $any*
@lident = $lower $any*
@number = [\-]? $digit+

:-

     $white+      ;  -- Skip white space
     "--".*       ;  -- Skip single-line comments

     ":"          { lexeme COLON }
     ";"          { lexeme SEMI }
     ","          { lexeme COMMA }
     "."          { lexeme DOT }
     "=>"         { lexeme RIGHTARROW }
     "("          { lexeme LPAREN }
     ")"          { lexeme RPAREN }
     "["          { lexeme LBRACK }
     "]"          { lexeme RBRACK }
     "{"          { lexeme LBRACE }
     "}"          { lexeme RBRACE }
     "link"       { lexeme LINK }
     "\"          { lexeme LAMBDA }
     "let"        { lexeme LET }
     "in"         { lexeme IN }
     "send"       { lexeme SEND }
     "receive"    { lexeme RECEIVE }
     "select"     { lexeme SELECT }
     "case"       { lexeme CASE }
     "of"         { lexeme OF }
     "terminate"  { lexeme TERMINATE }
     "serve"      { lexeme SERVE }
     "request"    { lexeme REQUEST }
     "sendType"   { lexeme SENDTYPE }
     "receiveType" {lexeme RECEIVETYPE }
     "fork"       { lexeme FORK }
     "unit"       { lexeme UNIT }

     "?"          { lexeme QUERY }
     "!"          { lexeme BANG }
     "*"          { lexeme TIMES }
     "+"          { lexeme PLUS }
     "&"          { lexeme AMP }
     "~"          { lexeme TILDE }
     "%"          { lexeme SERVER }
     "#"          { lexeme SERVICE }
     "end!"       { lexeme OUTTERM }
     "end?"       { lexeme INTERM}
     "-@"         { lexeme LINFUN }
     "->"         { lexeme UNLFUN }
     "Unit"       { lexeme UNITTYPE }

     "Int"        { lexeme INT }

     "|-"         { lexeme TURNSTILE }
     "="          { lexeme EQUALS }

     @uident      { identifier UIDENT }
     @lident      { identifier LIDENT }
     @number      { number }


{

data Token = LIDENT String
           | UIDENT String
           | COLON
           | SEMI
           | COMMA
           | DOT
           | RIGHTARROW
           | SLASH
           | LPAREN
           | RPAREN
           | LBRACK
           | RBRACK
           | LBRACE
           | RBRACE
           | LINK
           | LAMBDA
           | LET
           | IN
           | SEND
           | RECEIVE
           | SELECT
           | CASE
           | OF
           | TERMINATE
           | SERVE
           | REQUEST
           | SENDTYPE
           | RECEIVETYPE
           | FORK
           | UNIT 

           | BANG
           | QUERY
           | TIMES
           | PAR
           | PLUS
           | AMP
           | ONE
           | BOTTOM
           | TILDE
           | SERVER
           | SERVICE
           | OUTTERM
           | INTERM
           | LINFUN
           | UNLFUN
           | UNITTYPE

           | INT
           | INTCONST Integer

           | TURNSTILE
           | EQUALS

           | EOF

    deriving (Eq, Show)

lexeme :: Token -> AlexInput -> Int -> Alex Token
lexeme t _ len = return t

identifier :: (String -> Token) -> AlexInput -> Int -> Alex Token
identifier t (_, _, _, s) len = return (t (take len s))

number :: AlexInput -> Int -> Alex Token
number (_, _, _, s) len = return (INTCONST (read (take len s)))

alexEOF = return EOF

tokens str = runAlex str $ loop []
    where loop ts = do tok <- alexMonadScan
                       case tok of
                         EOF -> return (reverse ts)
                         _   -> loop (tok:ts)


}
