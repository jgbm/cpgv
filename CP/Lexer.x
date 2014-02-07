{
module CP.Lexer where
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
         "/"          { lexeme SLASH }
         "("          { lexeme LPAREN }
         ")"          { lexeme RPAREN }
         "["          { lexeme LBRACK }
         "]"          { lexeme RBRACK }
         "{"          { lexeme LBRACE }
         "}"          { lexeme RBRACE }
         "|"          { lexeme BAR }
         "<->"        { lexeme LINK }
         "cut"        { lexeme CUT }
         "case"       { lexeme CASE }
         "roll"       { lexeme ROLL }
         "unr"        { lexeme UNROLL }
         "?"          { lexeme QUERY }
         "!"          { lexeme BANG }

         "forall"     { lexeme FORALL }
         "exists"     { lexeme EXISTS }
         "mu"         { lexeme MU }
         "nu"         { lexeme NU }
         "*"          { lexeme TIMES }
         "||"         { lexeme PAR }
         "+"          { lexeme PLUS }
         "&"          { lexeme WITH }
         "bot"        { lexeme BOTTOM }
         "~"          { lexeme TILDE }

         "def"        { lexeme DEF }
         "type"       { lexeme TYPE }
         "|-"         { lexeme TURNSTILE }
         "="          { lexeme EQUALS }
         "check"      { lexeme CHECK }

         "\"          { lexeme LAMBDA }
         "bool"       { lexeme BOOL }
         "true"       { lexeme TRUE }
         "false"      { lexeme FALSE }
         "int"        { lexeme INT }
         "->"         { lexeme TO }
         "if"         { lexeme IF }
         "then"       { lexeme THEN }
         "else"       { lexeme ELSE }

         "<"          { lexeme LANGLE }
         ">"          { lexeme RANGLE }

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
           | SLASH
           | LPAREN
           | RPAREN
           | LBRACK
           | RBRACK
           | LBRACE
           | RBRACE
           | BAR
           | LINK
           | CUT
           | CASE
           | ROLL
           | UNROLL
           | QUERY
           | BANG

           | FORALL
           | EXISTS
           | MU
           | NU
           | TIMES
           | PAR
           | PLUS
           | WITH
           | BOTTOM
           | TILDE

           | DEF
           | TYPE
           | TURNSTILE
           | EQUALS
           | CHECK

           | LAMBDA
           | BOOL
           | TRUE
           | FALSE
           | INT
           | INTCONST Integer
           | TO
           | IF
           | THEN
           | ELSE

           | LANGLE
           | RANGLE

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
