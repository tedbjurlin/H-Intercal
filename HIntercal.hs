{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Main where


import Data.Void ( Void )
import Control.Monad ( (>=>), void, join )
import           Text.Megaparsec as P
import           Text.Megaparsec.Char ( space1, string )
import qualified Text.Megaparsec.Char.Lexer as L
import           Control.Monad.Combinators.Expr
    ( makeExprParser, Operator(InfixN) )
import qualified Data.Map as M
import           Data.List.Split ( splitOn )  -- nice library Dr. Yorgey O∧:
import           Data.Maybe ( fromMaybe )
import           Data.Bits ( Bits(xor, (.&.), (.|.)) )
import           System.Random ( randomRIO )
import           Data.Char (isSpace)
import           Data.Set (empty)
import           Control.Exception as E ( IOException, try )
import           System.IO
    ( hFlush, hSetBuffering, stdout, BufferMode(NoBuffering) )
import           System.Console.CmdArgs
    ( Data, Typeable, (&=), cmdArgs, help, summary, typ, Default(def) )

---------------------------------- Abstract Syntax Tree ----------------------------------

{- | Intercal is an imperitave language. As such, the main structure of the AST is a list
of commands to execute.
-}
type Prog = [Stmt]

{- | Commands in Intercal come in two forms. A `Stmt` is an parsed command that can be
executed by the interpreter. A `Cmnt` is any `Stmt` that failed to parse. After failing
parsing, it is stored as a `String`.
-}
data Stmt where
    {- | A `Stmt` ADT has five arguments:
    `Maybe Integer`: A line label, if present.
    `Bool`: Whether the line had a NOT quantifier. True if present.
    `Maybe Integer`: A percent quantifier if present. A `Stmt` will never have both a
        percent quantifier and a NOT quantifier.
    `StmtOp`: The `StmtOp` to be interpreted. This is the actual operation.
    `String`: The original `String` that was parsed, so that it may be printed
        unchanged in case of an error. This is because intercal can have a level of
        ambiguity that can be difficult to parse.
    -}
    Stmt :: Maybe Integer -> Bool -> Maybe Integer -> StmtOp -> String -> Stmt
    {- | A `Cmnt` ADT has three arguments:
    `Maybe Integer`: A line label, if present.
    `Bool`: Whether the line had a NOT quantifier. True if present.
    `String`: The unparseble string that formed the comment. Stored in case of errors.
    -}
    Cmnt :: Maybe Integer -> Bool -> String -> Stmt
    deriving Show

{- | A `StmtOp` is the part of a `Stmt` that actually gets executed. It represents every
operation that Intercal can complete.
-}
data StmtOp where
    {- | A `Calc` takes a variable or subscripted array and an expression, and assigns the
    result of the expression to the vairable.
    -}
    Calc       :: Exp -> Exp -> StmtOp
    {- | A `CalcDim` takes an array name and a list of expressions, and sets the array
    dimensions based on the result of the expressions.
    -}
    CalcDim    :: Exp -> [Exp] -> StmtOp
    {- | A `Next` statement takes an `Integer`, and attempts to move the program control to
    the line with the corresponding line label.
    -}
    Next       :: Integer -> StmtOp
    {- | A `Forget` statement takes an expression and attempts to remove the corresponding
    number of elements from the next stack.
    -}
    Forget     :: Exp -> StmtOp
    {- | A `Resume` statement does the same thing as a `Forget`, but also attempts to move
    program control to the last line removed from the next stack.
    -}
    Resume     :: Exp -> StmtOp
    {- | A `Stash` statement takes a list of variable names, and stashes the values of
    each variable in the corresponding stash stack.
    -}
    Stash      :: [Exp] -> StmtOp
    {- | A `Retrieve` statement takes a list of variables names, and attmepts to retrive each
    variables next value from the corresponding stash stack and set said value as the
    current value.
    -}
    Retrieve   :: [Exp] -> StmtOp
    {- | An `Ignore` statement takes a list of variable names, and sets those variables to
    be immutable.
    -}
    Ignore     :: [Exp] -> StmtOp
    {- | A `Remeber` statement takes a list of variable names, and sets those variables to
    be mutable.
    -}
    Remember   :: [Exp] -> StmtOp
    {- | An `Abstain` statement takes list of operation gerunds of the form 'NEXTING' or
    'IGNOREING' and prevents them from being executed in the future. `GiveUp` statements
    can not be abstained from.
    -}
    Abstain    :: [Gerund] -> StmtOp
    {- | An `AbstainL` statement is a variant of the `Abstain` statement that instead
    takes a single `Integer` line label and abstains from that particular line.
    -}
    AbstainL   :: Integer -> StmtOp
    {- | A `Reinstate` statement reinstates all the abstained operations in the list of
    gerunds so that they may be executed again.
    -}
    Reinstate  :: [Gerund] -> StmtOp
    {- | A `ReinstateL` statement reinstates a single line with the given `Integer` line
    label.
    -}
    ReinstateL :: Integer -> StmtOp
    {- | An `Output` statement outputs the values of all of the variables in the list of 
    variables give.
    -}
    Output     :: [Exp] -> StmtOp
    {- | An `Input` statement takes an input for each variable in the list of variables.
    -}
    Input      :: [Exp] -> StmtOp
    {- | A `GiveUp` statement is the only way to end program execution without throwing an
    error.
    -}
    GiveUp     :: StmtOp
    deriving Show

{- | `Exp`s indicate anything that can be in an expression: variables, constants and
operations. Variables and arrays can be either 16-bit or 32-bit and constants can only
be 16-bit. Any 32-bit values must be constructed with operations.
-}
data Exp where
    {- | The four variable types take an `Integer` variable name, which can be between
    1 and 65535
    -}
    Array16 :: Integer -> Exp
    Array32 :: Integer -> Exp
    Var16   :: Integer -> Exp
    Var32   :: Integer -> Exp
    {- | `Const`s take an `Integer` value between 0 and 65535. These values are checked
    during semantic checking.
    -}
    Const   :: Integer -> Exp
    {- | `Sub` expressions take an array and a list of expressions, and subsript the
    array by the result of the expressions.
    -}
    Sub     :: Exp -> [Exp] -> Exp
    {- | `Una` epressions take a unary operator and one operand, and apply the operator to
    the operand.
    -}
    Una     :: UOp -> Exp -> Exp
    {- | `Bin` expressions take a binary operator and two operands, and apply the operator
    to the operands.
    -}
    Bin     :: BOp -> Exp -> Exp -> Exp
    deriving (Show, Eq)

{- | `Gerund`s are used in `Abstain` and `Reinstate` statments to indicate which
operations to effect.
-}
data Gerund = Forgetting | Resuming | Stashing | Retrieving | Ignoring | Nexting
    | Remembering | Abstaining | Reinstating | Inputting | Outputting | Calculating
    deriving Show

{- | `UOp`s represent the three unary operators: AND, OR, and XOR. These operations
perform all of the corresponding boolean operation on all adjacent bits in the operand,
with the first and last bits going to the first bit.
-}
data UOp where
    AND :: UOp
    OR  :: UOp
    XOR :: UOp
    deriving (Show, Eq)

{- | `BOp`s represent the two binary operators: interleave and select. Interleave takes
two 16-bit values and returns a 32-bit value that alternates the bits of the two operands.
Select treats both operands as 32-bit values, and builds a new value by selecting only the
bits of the first operand that are ones in the second operand, and packs them to the
right. Easier said than done.
-}
data BOp where
    Ilv :: BOp
    Sel :: BOp
    deriving (Show, Eq)

----------------------------------------- Parser -----------------------------------------

type Parser = Parsec Void String

whitespace :: Parser ()
whitespace = L.space
  space1
  P.empty
  P.empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme whitespace

symbol :: String -> Parser String
symbol = L.symbol whitespace

integer :: Parser Integer
integer = lexeme L.decimal

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

reserved :: String -> Parser String
reserved w = (lexeme . P.try) (string w)

-- | Line labels take the form of an 16-bit, non-zero integer surrounded by parenthesis.
pLabel :: Parser Integer
pLabel = parens integer

{- | Identifiers can interchangebly take the form of PLEASE, PLEASE DO, or DO. They
signify the start of a statement, and may only be preceded by a line label. In some
versions of Intercal, errors would be raised if PLEASE was used too much or too little,
but I have not had time yet to implement politeness checks.
-}
pIdentifier :: Parser String
pIdentifier
    =   P.try ("PLEASE DO" <$ reserved "PLEASE" <* reserved "DO")
    <|> reserved "PLEASE"
    <|> reserved "DO"

{- | This parser is used to identify the beginning of a line, and will return the label
if present, otherwise Nothing.-}
pLabeledId :: Parser (Maybe Integer)
pLabeledId = optional pLabel <* pIdentifier

-- | This parser will True if there is a NOT quantifier, otherwise False.
pNot :: Parser Bool
pNot = option False (True <$ (reserved "NOT" <|> reserved "N'T"))

{- | This parse will parse percent quantifiers if present. They may be any natural number
less than or equal to 100.
-}
pPcnt :: Parser (Maybe Integer)
pPcnt = optional (symbol "%" *> integer)

{- | Array names are take the form of , followed by an integer for 16-bit, or ; for
32-bit.
-}
pArray :: Parser Exp
pArray
    =   Array16 <$> (symbol "," *> integer)
    <|> Array32 <$> (symbol ";" *> integer)

-- | Variable names use the same syntax as array names, but use . and : instead.
pVar :: Parser Exp
pVar
    =   Var16 <$> (symbol "." *> integer)
    <|> Var32 <$> (symbol ":" *> integer)

-- | Constants are written with a # followed by the constant value.
pConst :: Parser Exp
pConst = Const <$> (symbol "#" *> integer)

{- | Subscripts are written with an array name, followed by SUB, followed by a list of
single-term arrays
-}
pSub :: Parser Exp
pSub = Sub <$> (pArray <* reserved "SUB") <*> some pTerm

-- | this parser parses the Unary operator symbols
pUOp :: Parser UOp
pUOp
    =   AND <$ symbol "&"
    <|> OR  <$ symbol "V"
    <|> XOR <$ symbol "?"

{- | The unary operation parser parses both the operator and the variable that is being
operated on. This is because the operator is placed inside the variable name, so unary
operations cannot be parsed with the standard operation table method.
-}
pUna :: Parser Exp
pUna
    =   Una <$> (symbol "." *> pUOp) <*> (Var16 <$> integer)
    <|> Una <$> (symbol ":" *> pUOp) <*> (Var32 <$> integer)
    <|> Una
        <$> (symbol "," *> pUOp)
        <*> (Sub <$> ((Array16 <$> integer) <* reserved "SUB") <*> some pTerm)
    <|> Una
        <$> (symbol ";" *> pUOp)
        <*> (Sub <$> ((Array32 <$> integer) <* reserved "SUB") <*> some pTerm)
    <|> Una <$> (symbol "#" *> pUOp) <*> (Const <$> integer)

{- | The term parser parses a single term of an expression. That is, anything that is not
a binary operation, as binary operation involve two terms. This includes groupings.
Groupings were originally difficult to parse, as they consumed some of the input that they
took, but by wrapping them in try statements they worked properly. Because they use the
same opening and closing symbols, they introduce ambiguity into the meaning of certain
expressions. This is handled by having both sparks (') and rabbit ears ("") as symbols. By
alternating layers of sparks and rabbit ears, we can avoid ambiguity. Otherwise,
they will always tend to create a new group rather than close an existing one.
-}
pTerm :: Parser Exp
pTerm
    =   P.try (Una <$> (symbol "\'" *> pUOp) <*> (pExp <* symbol "\'"))
    <|> P.try (Una <$> (symbol "\"" *> pUOp) <*> (pExp <* symbol "\""))
    <|> P.try (between (symbol "\'") (symbol "\'") pExp)
    <|> P.try (between (symbol "\"") (symbol "\"") pExp)
    <|> P.try pUna
    <|> pVar
    <|> pConst
    <|> pSub

{- | We use a standard expression parser with an operator table to combine the terms with
the binary operators.
-}
pExp :: Parser Exp
pExp = makeExprParser pTerm operatorTable

operatorTable :: [[Operator Parser Exp]]
operatorTable =
  [ [ binary "$" (Bin Ilv)
    , binary "~" (Bin Sel)
    ]
  ]

binary :: String -> (Exp -> Exp -> Exp) -> Operator Parser Exp
binary  name f = InfixN  (f <$ symbol name)

{- | `Gerund`s are parsed using the reseved parser, which, contrary to its name, does not
actually reserve the strings that it parses. Intercal does not allow string variable
names, so there is no need to have reserved keywords in the language. The reserved parser
is instead used to allow us to parse a specific string.
-}
pGerund :: Parser Gerund
pGerund
    =   Forgetting <$ reserved "FORGETTING"
    <|> Resuming <$ reserved "RESUMING"
    <|> Stashing <$ reserved "STASHING"
    <|> Retrieving <$ reserved "RETRIEVING"
    <|> Ignoring <$ reserved "IGNORING"
    <|> Remembering <$ reserved "REMEMBERING"
    <|> Abstaining <$ reserved "ABSTAINING"
    <|> Reinstating <$ reserved "REINSTATING"
    <|> Inputting <$ reserved "INTPUTTING"
    <|> Outputting <$ reserved "OUTPUTTING"
    <|> Calculating <$ reserved "CALCULATING"
    <|> Nexting <$ reserved "NEXTING"

{- | This parse parses the individual statement operations. The parsers are set up to
match the structure of the statements defined in the Intercal Reference Manual. Not that
the `sepBy1` combinator is used to ensure that every list gets at least one item.
-}
pStmtOp :: Parser StmtOp
pStmtOp
    =   P.try (Calc       <$> ((pVar <|> pSub) <* reserved "<-") <*> pExp)
    <|> (CalcDim  <$> (pArray <* reserved "<-") <*> pExp `sepBy1` reserved "BY")
    <|> (Next     <$> (pLabel <* reserved "NEXT"))
    <|> (Forget   <$> (reserved "FORGET" *> pExp))
    <|> (Resume   <$> (reserved "RESUME" *> pExp))
    <|> (Stash    <$> (reserved "STASH" *> (pVar <|> pArray) `sepBy1` symbol "+"))
    <|> (Retrieve <$> (reserved "RETRIEVE" *> (pVar <|> pArray) `sepBy1` symbol "+"))
    <|> (Ignore   <$> (reserved "IGNORE" *> (pVar <|> pArray) `sepBy1` symbol "+"))
    <|> (Remember <$> (reserved "REMEMBER" *> (pVar <|> pArray) `sepBy1` symbol "+"))
    <|> (Abstain
        <$> P.try (reserved "ABSTAIN" 
            *> reserved "FROM" 
            *> (pGerund `sepBy1` symbol "+")))
    <|> (AbstainL   <$> (reserved "ABSTAIN" *> reserved "FROM" *> pLabel))
    <|> (Reinstate  <$> P.try (reserved "REINSTATE" *> (pGerund `sepBy1` symbol "+")))
    <|> (ReinstateL <$> (reserved "REINSTATE" *> pLabel))
    <|> (Input
        <$> (reserved "WRITE" *> reserved "IN" *> (pVar <|> pSub) `sepBy1` symbol "+"))
    <|> (Output
        <$> (reserved "READ"
            *> reserved "OUT"
            *> (pVar <|> pSub <|> pConst) `sepBy1` symbol "+"))
    <|> (GiveUp <$ reserved "GIVE" <* reserved "UP")

{- | The `pStmt` parser parse statements. It uses do notation to execute the individual
parsers for the parts of a statement, then compose them into one full result. The reason
for this is to allow the use of the `match` parser, which lets us get both the result of 
a parser and the consumed text. We can then combine the consumed text back into the
original statement string.
-}
pStmt :: Parser Stmt
pStmt = do
    (identifier, plabel) <- match pLabeledId
    (notq, qnot) <- match pNot
    (quantifier, quant) <- match pPcnt
    (stmtOp, sop) <- match pStmtOp
    return (Stmt plabel qnot quant sop (identifier++notq++quantifier++stmtOp))

{- | The `pCmnt` parser parses comments. It is structured similarly to the `pStmt` parser
above, but instead of applying parsers to build a statment, it uses the `manyTill` parser
to parse character literals unitl the next statement identifier or the end of the file.
This parser is called in the case that a statment cannot be parsed, so as to collect the
failed statment into a comment string. Note that comments can still have identifiers and
quantifiers, just not operations.
-}
pCmnt :: Parser Stmt
pCmnt = do
    (identifier, plabel) <- match (join <$> optional pLabeledId)
    (quantifier, pnot) <- match pNot
    comment <- manyTill L.charLiteral (eof <|> void (lookAhead pLabeledId))
    if identifier++quantifier++comment == ""
    then failure Nothing Data.Set.empty
    else return (Cmnt plabel pnot (identifier++quantifier++comment))

{- | The `pProg` parser repeatedly attempts to parse statments, and instead parses a 
comment if a statment fails. It uses a `try` combinator to ensure that the `pStmt` parser
does not consume the input unless it succeeds.
-}
pProg :: Parser Prog
pProg = many (P.try pStmt <|> pCmnt)

{- | `pWow` is intended to be run before the main Intercal parser to convert any wows (!)
into spots (.) followed by sparks ('). Note that rabbits are not allowed and therefore do
not need to be converted into spots and rabbit ears (")
-}
pWow :: String -> String
pWow []      = []
pWow ('!':s) = "'."++pWow s
pWow (c:s)   = c:pWow s

{- | `pIntercal` runs the `pProg` parser, while consuming preceding whitespace and ensuring
the input ends.
-}
pIntercal :: Parser Prog
pIntercal = whitespace *> pProg <* eof

------------------------------------ Semantic Checking -----------------------------------

{- | `Mem` is a map of `Integer` keys to `Integer` values. It is used to keep track of
the relation between labels and line names, as well as the value of variables (which all
have `Integer` names).
-}
type Mem = M.Map Integer Integer

{- | The `Error` type represents all of the errors that could be encountered in Intercal.
Intercal is unique in that parsing cannot raise errors: any issue in parsing results in
the creation of a comment. All errors are either raised during semantic checking or
interpreting.

Errors take one of two main forms, with only two exceptions: Either they take one
argument, the statement that would have been executed next, or no arguments, becuase it
is not possible to determine the next statement. The excetptions are `Err200Undecode`,
which is raised if comment without a NOT quanitifier is encountered, and takes both the
undecodeable statment and the next statement, and `Err579InvInput`, which is raised if an
invalid string is given as an input, and takes both the invalid string and the next
statement to be executed.
-}
data Error where
    Err000Undecode   :: Stmt -> Stmt -> Error
    Err017InvConst   :: Stmt -> Error
    Err079Impolite   :: Error
    Err099TooPolite  :: Error
    Err123Nexting    :: Error
    Err127SysLib     :: Error
    Err129UndefLabel :: Error
    Err139UndefARL   :: Stmt -> Error
    Err182MulLabel   :: Stmt -> Error
    Err197InvLabel   :: Stmt -> Error
    Err200InvVar     :: Stmt -> Error
    Err210InvRVar    :: Error
    Err240ArrDim0    :: Stmt -> Error
    Err241InvArrDim  :: Stmt -> Error
    Err275WrongSpot  :: Stmt -> Error
    Err436NotStashed :: Stmt -> Error
    Err533TooBig     :: Stmt -> Error
    Err562NoInput    :: Stmt -> Error
    Err579InvInput   :: String -> Stmt -> Error
    Err621E621       :: Stmt -> Error
    Err632TooResume  :: Error
    Err633ProgEnd    :: Error
    Err774RndBug     :: Error
    deriving Show

{- | The `checkSemantics` function checks that variable names, constant values, and labels
are within allowed values, and makes sure that every label referenced exists.
-}
checkSemantics :: Prog -> Mem -> Bool -> Either Error Bool
checkSemantics [] _ b = Right b

checkSemantics (Stmt _ _ _ (Calc e1 e2) _:s:p1) ls b
    =  checkExp e1 s
    *> checkExp e2 s
    *> checkSemantics (s:p1) ls b

checkSemantics ((Stmt _ _ _ (CalcDim e1 elst) _):s:p1) ls b
    =  checkExp e1 s
    *> checkExpList elst s
    *> checkSemantics (s:p1) ls b

checkSemantics ((Stmt _ _ _ (Next i) _):s:p1) ls b
  | M.member i ls = checkSemantics (s:p1) ls b
  | i >= 1_000 && i < 2_000 = checkSemantics (s:p1) ls True
  | otherwise = Left Err129UndefLabel

checkSemantics ((Stmt _ _ _ (Forget e) _):s:p1) ls b
    =  checkExp e s
    *> checkSemantics (s:p1) ls b

checkSemantics ((Stmt _ _ _ (Resume e) _):s:p1) ls b
    =  checkExpH e Err210InvRVar
    *> checkSemantics (s:p1) ls b

checkSemantics ((Stmt _ _ _ (Stash el) _):s:p1) ls b
    =  checkExpList el s
    *> checkSemantics (s:p1) ls b

checkSemantics ((Stmt _ _ _ (Retrieve el) _):s:p1) ls b
    =  checkExpList el s
    *> checkSemantics (s:p1) ls b

checkSemantics ((Stmt _ _ _ (Ignore el) _):s:p1) ls b
    =  checkExpList el s
    *> checkSemantics (s:p1) ls b

checkSemantics ((Stmt _ _ _ (Remember el) _):s:p1) ls b
    =  checkExpList el s
    *> checkSemantics (s:p1) ls b

checkSemantics ((Stmt _ _ _ (AbstainL i) _):s:p1) ls b =
    if i `M.member` ls
    then checkSemantics (s:p1) ls b
    else Left Err129UndefLabel

checkSemantics ((Stmt _ _ _ (ReinstateL i) _):s:p1) ls b =
    if i `M.member` ls
    then checkSemantics (s:p1) ls b
    else Left (Err139UndefARL s)

checkSemantics ((Stmt _ _ _ (Output el) _):s:p1) ls b
    =  checkExpList el s
    *> checkSemantics (s:p1) ls b

checkSemantics ((Stmt _ _ _ (Input el) _):s:p1) ls b
    =  checkExpList el s
    *> checkSemantics (s:p1) ls b

checkSemantics [Stmt _ _ _ (Resume e) _] ls b
    =  checkExpH e Err210InvRVar
    *> checkSemantics [] ls b

checkSemantics [Stmt _ _ _ (Next i) _] ls b =
    if i `M.member` ls
    then checkSemantics [] ls b
    else Left Err129UndefLabel

{- | Note that `getErrStmt` can only be used during interpreting, so some patterns won't
be matched, therefore a wildcard is necessary.
-}
checkSemantics (_:p1) ls b =  checkSemantics p1 ls b

{- | `checkLabels` runs before `checkSemantics`, and builds the map of labels to line
numbers. It also checks that line label names at the beginning of lines are correct.
-}
checkLabels :: Prog -> Mem -> Integer -> Either Error Mem
checkLabels [] m _ = Right m
checkLabels (Stmt (Just i) _ _ _ _:s:ls) m n
    =  checkN i 1 65_535 (Err197InvLabel s)
    *> if M.member i m
        then Left (Err182MulLabel s) else checkLabels (s:ls) (M.insert i n m) (n+1)
checkLabels (Cmnt (Just i) _ _:s:ls) m n
    =  checkN i 1 65_535 (Err197InvLabel s)
    *> if M.member i m
        then Left (Err182MulLabel s) else checkLabels (s:ls) (M.insert i n m) (n+1)
    {- | Error messages here inclued the current statment rather than the next one. This
    is because the next statment cannot be calculated consistently, and `checkErrStmt`
    was developed after this and has yet to be implemented here.
    -}
checkLabels (Stmt (Just i) q p s st:ls) m n
    =  checkN i 1 65_535 (Err197InvLabel (Stmt (Just i) q p s st))
    *> if M.member i m
        then Left (Err182MulLabel (Stmt (Just i) q p s st))
        else checkLabels ls (M.insert i n m) (n+1)
checkLabels (Cmnt (Just i) q s:ls) m n
    =  checkN i 1 65_535 (Err197InvLabel (Cmnt (Just i) q s))
    *> if M.member i m
        then Left (Err182MulLabel (Cmnt (Just i) q s))
        else checkLabels ls (M.insert i n m) (n+1)
checkLabels (_:ls) m n = checkLabels ls m (n+1)

-- | `checkExp` calls `checkExpH` with the standard error for invalid variables.
checkExp :: Exp -> Stmt -> Either Error ()
checkExp e s = checkExpH e (Err200InvVar s)

{- | `checkExpH` is checks the values of variable and array names, and recursively checks
the expressions in `Sub`, `Una`, and `Bin`.
-}
checkExpH :: Exp ->  Error -> Either Error ()
checkExpH (Array16 i) err   = checkN i 1 65_535 err
checkExpH (Array32 i) err   = checkN i 1 65_535 err
checkExpH (Var16 i) err     = checkN i 1 65_535 err
checkExpH (Var32 i) err     = checkN i 1 65_535 err
checkExpH (Const _) _       = Right () -- constants will be checked during runtime
checkExpH (Sub e el) err    = checkExpH e err *> checkExpListH el err
checkExpH (Una _ e) err     = checkExpH e err
checkExpH (Bin _ e1 e2) err = checkExpH e1 err *> checkExpH e2 err

-- | `checkExpList` runs `checkExpListH` with a default error
checkExpList :: [Exp] -> Stmt -> Either Error ()
checkExpList el s = checkExpListH el (Err200InvVar s)

-- | `checkExpList` applies `checkExpH` to a list of expressions, and takes an error.
checkExpListH :: [Exp] -> Error -> Either Error ()
checkExpListH [] _     = Right ()
checkExpListH (e:ls) err = checkExpH e err *> checkExpListH ls err

-- | `checkN` checks if a value is in the given range, and returns the given error.
checkN :: Integer -> Integer -> Integer -> Error -> Either Error ()
checkN i low high e = if (low <= i) && (i <= high) then Right () else Left e

-- | `checkProg` composes `checkLabels` with `checkSemantics`, and runs both.
checkProg :: Prog -> Either Error (Mem, Bool)
checkProg p = checkLabels p M.empty 0
    >>= \m -> checkSemantics p m False
        >>= \b -> Right (m, b)

---------------------------------------- Execution ---------------------------------------

-- | `ArrMem` maps `Integer` array names to `Array` values.
type ArrMem = M.Map Integer Array

-- | `StashVar` maps `Integer` variable names to stacks of stashed `Integer` values.
type StashVar = M.Map Integer [Integer]

-- | `StashArr` maps `Integer` array names to stacks of stashed `Array` values.
type StashArr = M.Map Integer [Array]

{- | `IgnMem` is used for both variables and arrays. It maps variable names to `Bool`s of
whether a variable is ignored. `True` indicates that a variable is ignored.
-}
type IgnMem = M.Map Integer Bool

{- | The `World` keeps track of all the memory used in interpreting. That includes
current variable values, stashed values, the relationship of labels to line numbers,
currently ignored values, and the stack of line numbers nexted from. Originally I was
also keeping track of a queue of input and output strings, but I realized that I had to
take input and give output at runtime, as it was impossible to compute ahead of time how
many times I would need to take input.

`Vars`, `Stashes`, and `Ignored` have been abstracted out into their own ADTs to make code
more readable.

Where it is used in the interpreter, the `World` looks like this when collapsed:
`W v st m3 iv ns`

And this when expanded:
`W (V m1 m2 am1 am2) (S sm1 sm2 sam1 sam2) m3 (I im1 im2 iam1 iam2) ns`
-}
data World where
    W  :: Vars       -- Variable values.
        -> Stashes   -- Variable stashes.
        -> Mem       -- Map of labels to line numbers.
        -> Ignored   -- Ignored variables.
        -> [Integer] -- Nexting stack.
        -> World
    deriving Show

-- | `Vars` keeps track of current variable values for the four types.
data Vars where
    V :: Mem         -- 16 bit memory
        -> Mem       -- 32 bit memory
        -> ArrMem    -- 16 bit arrays
        -> ArrMem    -- 32 bit arrays
        -> Vars
    deriving Show

-- | `Stashes` tracks stashed values for the four types of variables.
data Stashes where
    S :: StashVar    -- stashed 16 bit memory
        -> StashVar  -- stashed 32 bit memory
        -> StashArr  -- stashed 16 bit arrays
        -> StashArr  -- stashed 32 bit arrays
        -> Stashes
    deriving Show

-- | `Ignored` tracks whether the the variables are ignored.
data Ignored where
    I :: IgnMem       -- ignored 16 bit variables
        -> IgnMem     -- ignored 32 bit variables
        -> IgnMem     -- ignored 16 bit arrays
        -> IgnMem     -- ignored 32 bit arrays
        -> Ignored
    deriving Show

{- | The arrays are implemented by having an ADT with two constructors:

The `Single` constructor constructs an `Integer` array using a map of integer values and a
single integer value representing the size of the array. Array sizes are checked at
runtime. This constructor represents a one-dimesional array.

The `Multi` constuctor constructs an array of `Array`s using a map of `Integer`s to
`Array`s and a stack of `Integer` values, where the top one is the value of the current
dimension of the array, and the rest of the values are the subsequent nested arrays. This 
stack allows the arrays to be created as they are inserted, because the size is known
before the array is created. The `Multi` constructor represents the higher dimensions of a
multi dimesnional array.

Arrays are implemented recursively, despite the fact that there are probably better ways
to implement them. This method was chosen because it seemed more inline with the Intercal
design philosophy.
-}
data Array where
    Multi  :: [Integer] -> ArrMem -> Array
    Single :: Integer -> Mem -> Array
    deriving Show

{- | `composeIO` is a function to do the same thing as `(>>=)` that works inside IO
functions. I am not sure if there is something that already does this, or a preferred way
to do this in Haskell, but I couldn't find one.
-}
composeIO :: Either e a -> (a -> IO (Either e b)) -> IO (Either e b)
composeIO (Right a) f  = f a
composeIO (Left err) _ = return (Left err)

{- | `randomRIOERR` takes returns a random number between 0 and 1000. The lower bound is 
inclusive, and the upper bound is inclusive if the `Bool` parameter is True, and otherwise
exclusive. The `Bool` represents whether random compiler errors are enabled, and if the
generator generates exactly 1000, the interpreter throws a random compiler error.
-}
randomRIOERR :: Bool -> IO Integer
randomRIOERR True  = randomRIO (0, 1_000)
randomRIOERR False = randomRIO (0, 999)

{- | `rndPercent` uses the random number generator to determine whether a statement with
the percent quantifier should be run. It is also responsible for throwing the random
compiler error. This function is run for every statement, so the error could be thrown on
any line.
-}
rndPercent :: World -> Bool -> Maybe Integer -> IO (Either (World, Error) Bool)
rndPercent w b p = do
    r <- randomRIOERR b
    if r >= 1_000
    then return (Left (w, Err774RndBug))
    else case p of
        Just pcnt -> return (Right (r < pcnt * 10))
        Nothing   -> return (Right True)

{- | `interpProg` is the main interpreter function. It is responible for checking whether
a line is abstained, as well as raising an error if it encounters a non-abstained comment.
The `interpProg` function also calls `interpStmtOp` which does the heavy lifting of
interpretation.

Note that `interpProg`, `interpStmtOp` and many of thier sub-functions are IO types. This
is becuase input, output, and random number generation are not pure, and are needed in
some of the sub-functions.

It is important to note what the two `Prog` arguments are here, as it can be confusing.
The first one, p1, is the current statement and all the following ones yet to be
interpreted. The second one, p1, is all of the previously interpreted statements, with the
top one being the first line in the program. This convention is maintained throughout the
program.

The `Integer` argument is the current line number and the `Bool` indicates wheter random
compiler errors have been deactivated.
-}
interpProg :: World -> Bool -> Prog -> Prog -> Integer -> IO (Either (World, Error) World)
interpProg w _ [] _ _ = return (Left (w, Err633ProgEnd))
interpProg w b (Stmt l True p sop str:p1) p2 ln  = interpProg w b p1 (p2++[Stmt l True p sop str]) (ln+1)
interpProg w b (Stmt l q p sop str:p1) p2 ln      = do
    pcnt <- rndPercent w b p
    pcnt `composeIO` \b1 -> if b1
        then interpStmtOp sop w b (Stmt l q p sop str:p1) p2 ln
        else interpProg w b p1 (p2++[Stmt l q p sop str]) (ln+1)
interpProg w b (Cmnt l True s:p1) p2 ln      = interpProg w b p1 (p2++[Cmnt l True s]) (ln+1)
interpProg w _ (Cmnt l q s:p1) _ _            = getErrStmt w p1
    `composeIO` \stmt -> return (Left (w, Err000Undecode (Cmnt l q s) stmt))

{- | `interpStmtOp` does the heavy lifting of the interpreter, and uses pattern matching
interpret the different statment operations.

It takes the same arguments as `interpProg` with the addition of the current `Stmt`.
-}
interpStmtOp :: StmtOp -> World -> Bool -> Prog -> Prog -> Integer
    -> IO (Either (World, Error) World)

{- | `GiveUp` ends program execution without errors. Note that this is the only way to do
this, and all other methods of ending execution will raise an error.
-}
interpStmtOp GiveUp w _ _ _ _ = return (Right w)

{- | `Resume` and the following `Next` statement, are the reason that we have to keep
trakc of p2, the previously executed statements. This allows us to join p1 and p2 into
a the full program, and use `splitAt` to the program at the location we are moving
execution to.

This location is obtained from the `getStack` function, which pops items off the stack and
returns the last one.
-}
interpStmtOp (Resume e) w b p1 p2 _ = interpExp w p1 e
    `composeIO` \(i, _) -> getStack w i
        `composeIO` \(w1, idx) -> case splitAt (fromIntegral idx) (p2 ++ p1) of
            (p2', s' : p1') -> interpProg w1 b p1' (p2' ++ [s']) (idx + 1)
            (p2', [])       -> interpProg w1 b [] p2' (idx + 1)

{- | `Next` behaves similarly to `Resume`, except it instead adds the location that
execution was at before the next statement to the stack and moves to the indicated label.
It also handles the `Next` stack overflow, where an error is thrown if the `Next` stack
has 80 or more items.
-}
interpStmtOp (Next l) (W v s m3 iv ns) b p1 p2 idx = case M.lookup l m3 of
    Just idx1 ->
        if length ns >= 79
        then return (Left (W v s m3 iv ns, Err123Nexting))
        else case splitAt (fromIntegral idx1) (p2++p1) of
            (p2', [])  -> interpProg (W v s m3 iv (idx:ns)) b [] p2' idx1
            (p2', p1') -> interpProg (W v s m3 iv (idx:ns)) b p1' p2' idx1
    Nothing  -> return (Left (W v s m3 iv ns, Err129UndefLabel))

{- | `Calc` statements will intepret the given expression, and assign it to the given
variable. The only exception to this is if the variable is ignored, in which case
the `Calc` statement will do nothing.
-}
interpStmtOp (Calc v e) (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) b (s:p1) p2 idx = case v of
    
    {- | When calculating variables, the `calcVar` function is used to cut down on
    repeated code.
    -}
    (Var16 n) -> calcVar (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) p1 n 65_535
        e im1 m1 `composeIO` \m1' -> interpProg
            (W (V m1' m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) b p1 (p2++[s]) (idx+1)
    (Var32 n) -> calcVar (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) p1 n
        4_294_967_295 e im2 m2 `composeIO` \m2' -> interpProg
            (W (V m1 m2' am1 am2) st m3 (I im1 im2 iam1 iam2) ns) b p1 (p2++[s]) (idx+1)
    
    {- | Similarly, `calcArr` is used to calculate array insertion.
    -}
    (Sub (Array16 n) el) -> calcArr (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns)
        p1 n el 65_535 e iam1 am1 `composeIO` \am1' -> interpProg
            (W (V m1 m2 am1' am2) st m3 (I im1 im2 iam1 iam2) ns) b p1 (p2++[s]) (idx+1)
    (Sub (Array32 n) el) -> calcArr (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns)
        p1 n el 4_294_967_295 e iam2 am2 `composeIO` \am2' -> interpProg
            (W (V m1 m2 am1 am2') st m3 (I im1 im2 iam1 iam2) ns) b p1 (p2++[s]) (idx+1)
    
    {- | If a pattern is encountered that does not match a variable type, then it will
    raise an undecodable statement error. This should be completely prevented by the
    parser, so if this error is raised here something is going wrong up there.
    -}
    _ -> getErrStmt (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) p1
        `composeIO` \stmt -> return
            (Left (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns
            , Err000Undecode s stmt))

{- | `CalcDim` dimensions an array. This is done by calling the `calcDim` function on the
appropriate memory map. Similarly to `Calc` patterns that do not match an array raise an
undecodable statement error.
-}
interpStmtOp (CalcDim arr el) (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) b (s:p1) p2 idx = case arr of
    (Array16 n) -> calcDim (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) p1 n el iam1 am1
        `composeIO` \am1' -> interpProg (W (V m1 m2 am1' am2) st m3 (I im1 im2 iam1 iam2) ns)
            b p1 (p2++[s]) (idx+1)
    (Array32 n) -> calcDim (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) p1 n el iam2 am2
        `composeIO` \am2' -> interpProg (W (V m1 m2 am1 am2') st m3 (I im1 im2 iam1 iam2) ns)
            b p1 (p2++[s]) (idx+1)
    _           -> getErrStmt (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) p1
        `composeIO` \stmt -> return 
            (Left (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns
            , Err000Undecode s stmt))

{- | `Forget` uses `getStack` got get `i` items off of the stack, and discards them.
Unlike `Resume` it does not attempt to move to a different line.
-}
interpStmtOp (Forget e) w b (s:p1) p2 idx = interpExp w p1 e
    `composeIO` \(i, _) -> getStack w i
        `composeIO` \ (w1, _) -> interpProg w1 b p1 (p2++[s]) (idx + 1)

{- | The following four operations call their respective functions to perform their
operation on each variable in a list.
-}
interpStmtOp (Stash el) w b (s:p1) p2 idx = stashExpList w el s p1
    `composeIO` \w1 -> interpProg w1 b p1 (p2++[s]) (idx + 1)
interpStmtOp (Retrieve el) w b (s:p1) p2 idx = retrieveExpList w el s p1
    `composeIO` \w1 -> interpProg w1 b p1 (p2++[s]) (idx+1)
interpStmtOp (Ignore el) w b (s:p1) p2 idx = setIgnoreVarList w el s p1 True
    `composeIO` \w1 -> interpProg w1 b p1 (p2++[s]) (idx+1)
interpStmtOp (Remember el) w b (s:p1) p2 idx = setIgnoreVarList w el s p1 False
    `composeIO` \w1 -> interpProg w1 b p1 (p2++[s]) (idx+1)

{- | The following two operations take a list of gerunds, and call `setAbstainGerundList`
on the list, setting the gerunds to be either reinstated or abstained.
-}
interpStmtOp (Abstain gl) w b (s:p1) p2 idx = (\(p1', p2') -> interpProg w b p1' p2' (idx+1))
    (setAbstainGerundList gl True p1 (p2++[s]))
interpStmtOp (Reinstate gl) w b (s:p1) p2 idx = (\(p1', p2') -> interpProg w b p1' p2' (idx+1))
    (setAbstainGerundList gl False p1 (p2++[s]))

{- | The following two operations take a single line label and call their respective
functions to either abstain or reinstate that line.
-}
interpStmtOp (AbstainL la) w b (s:p1) p2 idx =
    abstainLabel w la (p2++[s]++p1) p1
        `composeIO` \p' -> (\(p2', p1') -> interpProg w b p1' p2' (idx+1))
            (splitAt (fromIntegral (idx+1)) p')
interpStmtOp (ReinstateL la) w b (s:p1) p2 idx =
    reinstateLabel w la (p2++[s]++p1) p1
        `composeIO` \p' -> (\(p2', p1') -> interpProg w b p1' p2' (idx+1))
            (splitAt (fromIntegral (idx+1)) p')

{- | The `Input` operation takes a list of variables and calls `takeInputList` to take
input for each variable.
-}
interpStmtOp (Input el) w b (s:p1) p2 idx = do
    we <- takeInputList w p1 el
    we `composeIO` \w1 -> interpProg w1 b p1 (p2++[s]) (idx+1)

{- | The `Output` operation reads out the values of each variable in the list by calling
`writeOutputList`.
-}
interpStmtOp (Output el) w b (s:p1) p2 idx = do
    writeOutputList w p1 el >> interpProg w b p1 (p2++[s]) (idx+1)

{- | An empty program raises the program end error.
-}
interpStmtOp _ w _ [] _ _ = return (Left (w, Err633ProgEnd))

{- | `calcVar` assigns the input expression to the given variable memory.
It skips ignored variables and raises an error if the variable is of the wrong type.
-}
calcVar :: World -> Prog -> Integer -> Integer -> Exp -> IgnMem -> Mem -> Either (World, Error) Mem
calcVar w p1 v mx e im m = if fromMaybe False (M.lookup v im)
        then Right m
        else interpExp w p1 e >>= \(val, _) ->
            if val > mx
            then getErrStmt w p1 >>= \stmt -> if mx == 65_535
                then Left (w, Err275WrongSpot stmt)
                else Left (w, Err533TooBig stmt)
            else Right (M.insert v val m)

{- | Similarly, `calcArr` assigns the input expression to the given array memory. It does
this by taking the array out of memory and inserting the value into the array. It also
skips ignored variables and raises an error if the value is too large.
-}
calcArr :: World -> Prog -> Integer -> [Exp] -> Integer -> Exp -> IgnMem -> ArrMem
    -> Either (World, Error) ArrMem
calcArr w p1 v el mx e im am = if fromMaybe False (M.lookup v im)
        then Right am
        else interpExp w p1 e
            >>= \(val, _) ->
                if val > mx
                then getErrStmt w p1
                    >>= \stmt -> if mx == 65_535
                        then Left (w, Err275WrongSpot stmt)
                        else Left (w, Err533TooBig stmt)
                else interpExpList w p1 el
                    >>= \il -> case M.lookup v am of
                        Just arr -> insertArray
                            w p1 arr val il
                                >>= \arr1 -> Right (M.insert v arr1 am)
                        Nothing -> getErrStmt w p1
                            >>= \stmt -> Left (w, Err200InvVar stmt)

{- | `calcDim` creates a new array that does not have any dimensions of 0 and inserts
it into the give array memory.
-}
calcDim :: World -> Prog -> Integer -> [Exp] -> IgnMem -> ArrMem -> Either (World, Error) ArrMem
calcDim w p1 arr el im am = if fromMaybe False (M.lookup arr im)
        then Right am
        else interpExpList w p1 el
            >>= \il -> case (il, 0 `elem` il) of
                (_, True) -> getErrStmt w p1
                    >>= \stmt -> Left (w, Err240ArrDim0 stmt)
                ([], _) -> getErrStmt w p1
                    >>= \stmt -> Left (w, Err240ArrDim0 stmt)
                ([m], _) -> Right (M.insert arr (Single m M.empty) am)
                _ -> Right (M.insert arr (Multi il M.empty) am)

{- | `insertArray` recursively climbs down an array by the list of indexes until it
reaches the end of this list of indexes, then inserts the integer at the last index.
If the last index is not a `Single` array, or it reaches a `Single` array before the end
of the list of indexes, an array is raised. An error is also raised if the index is out of
the bounds of the array.

Due to the way that the `Array` type is implemented, when an array is created, the values
and sub-arrays are not initialized. Therefore, when `insertArray` encounters an
uninitialized value or array, it sets it to the default value, 0.
-}
insertArray :: World -> Prog -> Array -> Integer -> [Integer] -> Either (World, Error) Array
insertArray w p _ _ []    = getErrStmt w p >>= \stmt -> Left (w, Err241InvArrDim stmt)
insertArray w p (Single l m) val [idx] =
    if idx < l
    then Right (Single l (M.insert idx val m))
    else getErrStmt w p >>= \stmt -> Left (w, Err241InvArrDim stmt)
insertArray w p (Multi _ _) _ [_] = getErrStmt w p >>= \stmt -> Left (w, Err241InvArrDim stmt)
insertArray w p (Multi [l1, l2] m) val (idx:idl) =
    if idx < l1
    then insertArray w p (fromMaybe (Single l2 M.empty) (M.lookup idx m)) val idl
        >>= \arr -> Right (Multi [l1, l2] (M.insert idx arr m))
    else getErrStmt w p >>= \stmt -> Left (w, Err241InvArrDim stmt)
insertArray w p (Multi (l1:ll) m) val (idx:idl) =
    if idx < l1
    then insertArray w p (fromMaybe (Multi ll M.empty) (M.lookup idx m)) val idl
        >>= \arr -> Right (Multi (l1:ll) (M.insert idx arr m))
    else getErrStmt w p >>= \stmt -> Left (w, Err241InvArrDim stmt)
insertArray w p _ _ _ = getErrStmt w p >>= \stmt -> Left (w, Err241InvArrDim stmt)

{- | `retrieveArray` retrieves a value from an array by recursively descending the array.
It will raise an error if the array has not been dimensioned or if the list of indexes
does not match the dimesnions of the array.
-}
retrieveArray :: World -> Prog -> Array -> [Integer] -> Either (World, Error) Integer
retrieveArray w p _ [] = getErrStmt w p >>= \stmt -> Left (w, Err241InvArrDim stmt)
retrieveArray w p (Single l m) [idx] =
    if idx < l
    then case M.lookup idx m of
        Just n  -> Right n
        Nothing -> getErrStmt w p >>= \stmt -> Left (w, Err200InvVar stmt)
    else getErrStmt w p >>= \stmt -> Left (w, Err241InvArrDim stmt)
retrieveArray w p (Multi _ _) [_] =
    getErrStmt w p >>= \stmt -> Left (w, Err241InvArrDim stmt)
retrieveArray w p (Multi (l1:_) m) (idx:idl) =
    if idx < l1
    then case M.lookup idx m of
        Just arr -> retrieveArray w p arr idl
        Nothing  -> getErrStmt w p >>= \stmt -> Left (w, Err200InvVar stmt)
    else getErrStmt w p >>= \stmt -> Left (w, Err241InvArrDim stmt)
retrieveArray w p _ _ = getErrStmt w p >>= \stmt -> Left (w, Err241InvArrDim stmt)

{- | `stashExpList` calls `stashVar` or `stashArr` on the correct memory for the type of each variable
in the give list of variables.
-}
stashExpList :: World -> [Exp] -> Stmt -> Prog -> Either (World, Error) World
stashExpList w [] _ _ = Right w
stashExpList (W (V m1 m2 am1 am2) (S sm1 sm2 sam1 sam2) m3 iv ns) (Var16 n:ls) s p =
    stashVar n m1 sm1
        >>= \sm -> stashExpList
            (W (V m1 m2 am1 am2) (S sm sm2 sam1 sam2) m3 iv ns)
            ls s p
stashExpList (W (V m1 m2 am1 am2) (S sm1 sm2 sam1 sam2) m3 iv ns) (Var32 n:ls) s p =
    stashVar n m2 sm2
        >>= \sm -> stashExpList
            (W (V m1 m2 am1 am2) (S sm1 sm sam1 sam2) m3 iv ns)
            ls s p
stashExpList (W (V m1 m2 am1 am2) (S sm1 sm2 sam1 sam2) m3 iv ns) (Array16 n:ls) s p =
    stashArr n am1 sam1
        >>= \sm -> stashExpList
            (W (V m1 m2 am1 am2) (S sm1 sm2 sm sam2) m3 iv ns)
            ls s p
stashExpList (W (V m1 m2 am1 am2) (S sm1 sm2 sam1 sam2) m3 iv ns) (Array32 n:ls) s p =
    stashArr n am2 sam2
        >>= \sm -> stashExpList
            (W (V m1 m2 am1 am2) (S sm1 sm2 sam1 sm) m3 iv ns)
            ls s p
stashExpList w _ s p = getErrStmt w p >>= \st -> Left (w, Err000Undecode s st)

{- | `stashVar` stashes non-array variables. It takes the variable name, the var memory
and the stash memory and returns the memory with the stashed variable.

A behavior of stash that was not defined in the Intercal refernce manual but is necessary
for the functioning of the standard library, is that if an attempt is made to stach an
undefined variable, a default value will instead be inserted. I assume that this is
because in the architecture that Intercal was designed for, every variable name would be
assigned to a default value, rather than being undefined.
-}
stashVar :: Integer -> Mem -> M.Map Integer [Integer] -> Either (World, Error) (M.Map Integer [Integer])
stashVar n m1 sm1 = case M.lookup n m1 of
    Just var -> case M.lookup n sm1 of
        Just il -> Right (M.insert n (var:il) sm1)
        Nothing -> Right (M.insert n [var] sm1)
    Nothing  -> case M.lookup n sm1 of
        Just il  -> Right (M.insert n (0:il) sm1)
        Nothing -> Right (M.insert n [0] sm1)

{- | `stashArr` stashes arrays in the same way as variables are stashed.

I extrapolated the behavior from `stashVar` to `stashArr` and had the default for a
stashed array be an empty `Single` array with a size of one. I am not sure if this is
correct since it is much more difficult to guess the default value of a collection of
infinite size, but it works so I guess it's fine.
-}
stashArr :: Integer -> ArrMem -> M.Map Integer [Array] -> Either (World, Error) (M.Map Integer [Array])
stashArr n m1 sm1 = case M.lookup n m1 of
    Just var -> case M.lookup n sm1 of
        Just il -> Right (M.insert n (var:il) sm1)
        Nothing -> Right (M.insert n [var] sm1)
    Nothing  -> case M.lookup n sm1 of
        Just il  -> Right (M.insert n (Single 1 M.empty:il) sm1)
        Nothing -> Right (M.insert n [Single 1 M.empty] sm1)

{- | `retrieveExpList` calls `retrieveVar` on each item in the given list. Note that there
is only one function for retriving since there is not difference between retrieving a
variable or array.
-}
retrieveExpList :: World -> [Exp] -> Stmt -> Prog -> Either (World, Error) World
retrieveExpList w [] _ _ = Right w
retrieveExpList (W (V m1 m2 am1 am2) (S sm1 sm2 sam1 sam2) m3 (I im1 im2 iam1 iam2) ns) (Var16 n:ls) s p =
    retrieveVar (W (V m1 m2 am1 am2) (S sm1 sm2 sam1 sam2) m3 (I im1 im2 iam1 iam2) ns) p n sm1 m1 im1
        >>= \(m, sm) -> retrieveExpList
            (W (V m m2 am1 am2) (S sm sm2 sam1 sam2) m3 (I im1 im2 iam1 iam2) ns)
            ls s p
retrieveExpList (W (V m1 m2 am1 am2) (S sm1 sm2 sam1 sam2) m3 (I im1 im2 iam1 iam2) ns) (Var32 n:ls) s p =
    retrieveVar (W (V m1 m2 am1 am2) (S sm1 sm2 sam1 sam2) m3 (I im1 im2 iam1 iam2) ns) p n sm2 m2 im2
        >>= \(m, sm) -> retrieveExpList
            (W (V m1 m am1 am2) (S sm1 sm sam1 sam2) m3 (I im1 im2 iam1 iam2) ns)
            ls s p
retrieveExpList (W (V m1 m2 am1 am2) (S sm1 sm2 sam1 sam2) m3 (I im1 im2 iam1 iam2) ns) (Array16 n:ls) s p =
    retrieveVar (W (V m1 m2 am1 am2) (S sm1 sm2 sam1 sam2) m3 (I im1 im2 iam1 iam2) ns) p n sam1 am1 iam1
        >>= \(m, sm) -> retrieveExpList
            (W (V m1 m2 m am2) (S sm1 sm2 sm sam2) m3 (I im1 im2 iam1 iam2) ns)
            ls s p
retrieveExpList (W (V m1 m2 am1 am2) (S sm1 sm2 sam1 sam2) m3 (I im1 im2 iam1 iam2) ns) (Array32 n:ls) s p =
    retrieveVar (W (V m1 m2 am1 am2) (S sm1 sm2 sam1 sam2) m3 (I im1 im2 iam1 iam2) ns) p n sam2 am2 iam2
        >>= \(m, sm) -> retrieveExpList (W (V m1 m2 am1 m) (S sm1 sm2 sam1 sm) m3 (I im1 im2 iam1 iam2) ns)
            ls s p
retrieveExpList w _ s p = getErrStmt w p >>= \st -> Left (w, Err000Undecode s st)

{- | `retriveVar` retrives a variable from the stash stack and inserts it into the var
memory.

There is some ambiguity around retreive in the Intercal reference manual, specifically
around whether ignore should apply to retrieve. In classic Intercal fashion, every current
Intercal compiler handles this ambiguity differently. My compiler simply does nothing if
a variable to be retrieved is currently ignored. No entries are removed from the stack
and the ignored variable is not changed. This differs from the other compilers, who's
behavior can be found in the C-Intercal docs.
-}
retrieveVar :: World -> Prog -> Integer -> M.Map Integer [b] -> M.Map Integer b -> IgnMem -> Either (World, Error) (M.Map Integer b, M.Map Integer [b])
retrieveVar w p n sm1 m1 im1 = 
    if fromMaybe False (M.lookup n im1)
    then Right (m1, sm1)
    else case M.lookup n sm1 of
        Just (var:il) -> Right (M.insert n var m1, M.insert n il sm1)
        Just []       -> getErrStmt w p >>= \s -> Left (w, Err436NotStashed s)
        Nothing  -> getErrStmt w p >>= \s -> Left (w, Err436NotStashed s)

{- | `setIgnoreVarList` sets the boolean value of whether each variable in the given list
is ignored in the ingore memory.
-}
setIgnoreVarList :: World -> [Exp] -> Stmt -> Prog -> Bool -> Either (World, Error) World -- can be combined with remember
setIgnoreVarList w [] _ _ _ = Right w
setIgnoreVarList (W v st m3 (I im1 im2 iam1 iam2) ns) (Var16 n:el) s p b =
    setIgnoreVarList (W v st m3 (I (M.insert n b im1) im2 iam1 iam2) ns) el s p b
setIgnoreVarList (W v st m3 (I im1 im2 iam1 iam2) ns) (Var32 n:el) s p b =
    setIgnoreVarList (W v st m3 (I im1 (M.insert n b im2) iam1 iam2) ns) el s p b
setIgnoreVarList (W v st m3 (I im1 im2 iam1 iam2) ns) (Array16 n:el) s p b =
    setIgnoreVarList (W v st m3 (I im1 im2 (M.insert n b iam1) iam2) ns) el s p b
setIgnoreVarList (W v st m3 (I im1 im2 iam1 iam2) ns) (Array32 n:el) s p b =
    setIgnoreVarList (W v st m3 (I im1 im2 iam1 (M.insert n b iam2)) ns) el s p b
setIgnoreVarList w _ s p _ = getErrStmt w p
    >>= \stmt -> Left (w, Err000Undecode s stmt)

{- | `setAbstainGerundList` iterates through a list of `Gerund`s and calls
`setAbstainGerund` on each one.
-}
setAbstainGerundList :: [Gerund] -> Bool -> Prog -> Prog -> (Prog, Prog)
setAbstainGerundList [] _ p1 p2 = (p1, p2)
setAbstainGerundList (g:gl) b p1 p2 = setAbstainGerundList gl b (setAbstainGerund g b p1 [])
    (setAbstainGerund g b p2 [])

{- | `setAbstainGerund` iterates through the given program and sets the Not qunatifier to
the given boolean for each matching statement.
-}
setAbstainGerund :: Gerund -> Bool -> Prog -> Prog -> Prog
setAbstainGerund _ _ [] p2 = p2
setAbstainGerund Forgetting b (Stmt l _ p (Forget el) str:p1) p2 =
    setAbstainGerund Forgetting b p1 (p2++[Stmt l b p (Forget el) str])
setAbstainGerund Resuming b (Stmt l _ p (Resume e) str:p1) p2 =
    setAbstainGerund Resuming b p1 (p2++[Stmt l b p (Resume e) str])
setAbstainGerund Stashing b (Stmt l _ p (Stash el) str:p1) p2 =
    setAbstainGerund Stashing b p1 (p2++[Stmt l b p (Stash el) str])
setAbstainGerund Retrieving b (Stmt l _ p (Retrieve el) str:p1) p2 =
    setAbstainGerund Retrieving b p1 (p2++[Stmt l b p (Retrieve el) str])
setAbstainGerund Ignoring b (Stmt l _ p (Ignore el) str:p1) p2 =
    setAbstainGerund Ignoring b p1 (p2++[Stmt l b p (Ignore el) str])
setAbstainGerund Remembering b (Stmt l _ p (Remember el) str:p1) p2 =
    setAbstainGerund Remembering b p1 (p2++[Stmt l b p (Remember el) str])
setAbstainGerund Abstaining b (Stmt l _ p (Abstain el) str:p1) p2 =
    setAbstainGerund Abstaining b p1 (p2++[Stmt l b p (Abstain el) str])
setAbstainGerund Abstaining b (Stmt l _ p (AbstainL la) str:p1) p2 =
    setAbstainGerund Abstaining b p1 (p2++[Stmt l b p (AbstainL la) str])
setAbstainGerund Reinstating b (Stmt l _ p (Reinstate el) str:p1) p2 =
    setAbstainGerund Reinstating b p1 (p2++[Stmt l b p (Reinstate el) str])
setAbstainGerund Reinstating b (Stmt l _ p (ReinstateL la) str:p1) p2 =
    setAbstainGerund Reinstating b p1 (p2++[Stmt l b p (ReinstateL la) str])
setAbstainGerund Inputting b (Stmt l _ p (Input el) str:p1) p2 =
    setAbstainGerund Inputting b p1 (p2++[Stmt l b p (Input el) str])
setAbstainGerund Outputting b (Stmt l _ p (Output el) str:p1) p2 =
    setAbstainGerund Outputting b p1 (p2++[Stmt l b p (Output el) str])
setAbstainGerund Calculating b (Stmt l _ p (Calc e el) str:p1) p2 =
    setAbstainGerund Calculating b p1 (p2++[Stmt l b p (Calc e el) str])
setAbstainGerund Calculating b (Stmt l _ p (CalcDim e el) str:p1) p2 =
    setAbstainGerund Calculating b p1 (p2++[Stmt l b p (CalcDim e el) str])
setAbstainGerund Nexting b (Stmt l _ p (Next el) str:p1) p2 =
    setAbstainGerund Nexting b p1 (p2++[Stmt l b p (Next el) str])
setAbstainGerund g b (s:p1) p2 = setAbstainGerund g b p1 (p2++[s])

-- | `abstainLabel` sets the NOT quantifier of the given label to True.
abstainLabel :: World -> Integer -> Prog -> Prog -> Either (World, Error) Prog
abstainLabel (W v st m3 iv ns) l p nx = case M.lookup l m3 of
    Just idx -> case splitAt (fromIntegral idx) p of
        (_, []) ->
            getErrStmt (W v st m3 iv []) nx
                >>= \stmt -> Left (W v st m3 iv ns, Err139UndefARL stmt)
        (p1, (Stmt la _ pe sop str):p2) -> Right (p1++[Stmt la True pe sop str]++p2)
        (p1, (Cmnt la _ str):p2)   -> Right (p1++[Cmnt la True str]++p2)
    Nothing -> getErrStmt (W v st m3 iv []) nx
                >>= \stmt -> Left (W v st m3 iv ns, Err139UndefARL stmt)

{- | `reinstateLabel` sets the NOT quantifier of the given label to False. It would be the
same function as `abstainLabel` but `GiveUp` statements can be abstained but not
reinstated.
-}
reinstateLabel :: World -> Integer -> Prog -> Prog -> Either (World, Error) Prog
reinstateLabel (W v st m3 iv ns) l p nx = case M.lookup l m3 of
    Just idx -> case splitAt (fromIntegral idx) p of
        (_, []) ->
            getErrStmt (W v st m3 iv []) nx
                >>= \stmt -> Left (W v st m3 iv ns, Err139UndefARL stmt)
        (_, (Stmt _ _ _ GiveUp _):_) -> Right p
        (p1, (Stmt la _ pe sop str):p2)  -> Right (p1++[Stmt la False pe sop str]++p2)
        (p1, (Cmnt la _ str):p2)     -> Right (p1++[Cmnt la False str]++p2)
    Nothing -> getErrStmt (W v st m3 iv []) nx
                >>= \stmt -> Left (W v st m3 iv ns, Err139UndefARL stmt)

{- | 
-}
interpExpList :: World -> Prog -> [Exp] -> Either (World, Error) [Integer]
interpExpList _ _ []     = Right []
interpExpList w p (e:el) = interpExp w p e >>= \(i, _) -> interpExpList w p el >>= \il -> Right (i:il)

takeInputList :: World -> Prog -> [Exp] -> IO (Either (World, Error) World)
takeInputList w _ [] = return (Right w)
takeInputList (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) p (Var16 n:es) = do
    wm <- takeInputVar (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) p True n m1 im1
    wm `composeIO` \(W (V _ nm2 nam1 nam2) nst nm3 iv nns, newm1) -> takeInputList
        (W (V newm1 nm2 nam1 nam2) nst nm3 iv nns)
        p
        es
takeInputList (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) p (Var32 n:es) = do 
    wm <- takeInputVar (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) p False n m2 im2
    wm `composeIO` \(W (V nm1 _ nam1 nam2) nst nm3 iv nns, newm2) -> takeInputList
        (W (V nm1 newm2 nam1 nam2) nst nm3 iv nns)
        p
        es
takeInputList (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) p (Sub (Array16 n) el:es) =
    interpExpList (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) p el
        `composeIO` \il -> do
            wm <- takeInputArr
                (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) p True n il am1 iam1
            wm `composeIO` \(W (V nm1 nm2 _ nam2) nst nm3 (I nim1 nim2 niam1 niam2) nns, newm1) -> takeInputList
                (W (V nm1 nm2 newm1 nam2) nst nm3 (I nim1 nim2 niam1 niam2) nns)
                p
                es
takeInputList (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) p (Sub (Array32 n) el:es) =
    interpExpList (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) p el
        `composeIO` \il -> do
            wm <- takeInputArr
                (W (V m1 m2 am1 am2) st m3 (I im1 im2 iam1 iam2) ns) p False n il am2 iam2
            wm `composeIO` \(W (V nm1 nm2 nam1 _) nst nm3 (I nim1 nim2 niam1 niam2) nns, newm2) -> takeInputList
                (W (V nm1 nm2 nam1 newm2) nst nm3 (I nim1 nim2 niam1 niam2) nns)
                p
                es
takeInputList w p _ = getErrStmt w p `composeIO` \stmt -> return (Left (w, Err017InvConst stmt))

takeInputVar :: World -> Prog -> Bool -> Integer -> Mem -> IgnMem -> IO (Either (World, Error) (World, Mem))
takeInputVar (W v st m3 iv ns) p vt n m im = do
    inp <- getLine
    if fromMaybe False (M.lookup n im)
    then return (Right (W v st m3 iv ns, m))
    else return (parseInput (W v st m3 iv ns) p inp
        >>= \num -> if vt   then if num < 65_536
                then Right (W v st m3 iv ns, M.insert n num m)
                else getErrStmt (W v st m3 iv ns) p
                    >>= \stmt -> Left (W v st m3 iv ns, Err275WrongSpot stmt)
            else if num < 4_294_967_295
                then Right (W v st m3 iv ns, M.insert n num m)
                else getErrStmt (W v st m3 iv ns) p
                    >>= \stmt -> Left (W v st m3 iv ns, Err533TooBig stmt))

takeInputArr :: World -> Prog -> Bool -> Integer -> [Integer] -> ArrMem -> IgnMem -> IO (Either (World, Error) (World, ArrMem))
takeInputArr (W v st m3 iv ns) p vt n nl m im = do
    inp <- getLine
    if fromMaybe False (M.lookup n im)
    then return (Right (W v st m3 iv ns, m))
    else return (parseInput (W v st m3 iv ns) p inp
        >>= \num -> case M.lookup n m of
            Just arr -> if vt
                then if num < 65_536
                    then insertArray (W v st m3 iv ns) p arr num nl
                        >>= \narr -> Right (W v st m3 iv ns, M.insert n narr m)
                    else getErrStmt (W v st m3 iv ns) p
                        >>= \stmt -> Left (W v st m3 iv ns, Err275WrongSpot stmt)
                else if num < 42_94_967_295
                    then insertArray (W v st m3 iv ns) p arr num nl
                        >>= \narr -> Right (W v st m3 iv ns, M.insert n narr m)
                    else getErrStmt (W v st m3 iv ns) p
                        >>= \stmt -> Left (W v st m3 iv ns, Err533TooBig stmt)
            Nothing  -> getErrStmt (W v st m3 iv ns) p
                >>= \stmt -> Left (W v st m3 iv ns, Err200InvVar stmt))

parseInput :: World -> Prog -> String -> Either (World, Error) Integer
parseInput w p [] = getErrStmt w p >>= \stmt -> Left (w, Err562NoInput stmt)
parseInput w p s  = parseInputNums w p (splitOn " " s) 0

writeOutputList :: World -> Prog -> [Exp] -> IO (Either (World, Error) ())
writeOutputList _ _ []     = return (Right ())
writeOutputList w p (e:el) = writeOutput w p e `composeIO` (\out -> out >> writeOutputList w p el)

writeOutput :: World -> Prog -> Exp -> Either (World, Error) (IO ())
writeOutput (W (V m1 m2 am1 am2) st m3 iv ns) p (Var16 n) = case M.lookup n m1 of
    Just i1 -> Right $ putStrLn (showOutput i1 i1) >> hFlush stdout
    Nothing -> getErrStmt (W (V m1 m2 am1 am2) st m3 iv ns) p
        >>= \stmt -> Left (W (V m1 m2 am1 am2) st m3 iv ns, Err200InvVar stmt)
writeOutput (W (V m1 m2 am1 am2) st m3 iv ns) p (Var32 n) = case M.lookup n m2 of
    Just i1 -> Right $ putStrLn (showOutput i1 i1) >> hFlush stdout
    Nothing -> getErrStmt (W (V m1 m2 am1 am2) st m3 iv ns) p
        >>= \stmt -> Left (W (V m1 m2 am1 am2) st m3 iv ns, Err200InvVar stmt)
writeOutput (W (V m1 m2 am1 am2) st m3 iv ns) p (Sub (Array16 n) el) = case M.lookup n am1 of
    Just arr -> interpExpList (W (V m1 m2 am1 am2) st m3 iv ns) p el
        >>= (retrieveArray (W (V m1 m2 am1 am2) st m3 iv ns) p arr
        >=>
          (\ i1
            -> Right $ putStrLn (showOutput i1 i1) >> hFlush stdout))
    Nothing -> getErrStmt (W (V m1 m2 am1 am2) st m3 iv ns) p
        >>= \stmt -> Left (W (V m1 m2 am1 am2) st m3 iv ns, Err200InvVar stmt)
writeOutput (W (V m1 m2 am1 am2) st m3 iv ns) p (Sub (Array32 n) el) = case M.lookup n am2 of
    Just arr -> interpExpList (W (V m1 m2 am1 am2) st m3 iv ns) p el
        >>= (retrieveArray (W (V m1 m2 am1 am2) st m3 iv ns) p arr
        >=>
          (\ i1
            -> Right $ putStrLn (showOutput i1 i1) >> hFlush stdout))
    Nothing -> getErrStmt (W (V m1 m2 am1 am2) st m3 iv ns) p
        >>= \stmt -> Left (W (V m1 m2 am1 am2) st m3 iv ns, Err200InvVar stmt)
writeOutput _ _ (Const i1) = Right $ putStrLn (showOutput i1 i1) >> hFlush stdout
writeOutput w p _ = getErrStmt w p >>= \stmt -> Left (w, Err200InvVar stmt)


showOutput :: Integer -> Integer -> String
showOutput i n
    | n == 0             = "\x305"
    | i >= 4_000_000_000 = "i\x305" ++ "v\x305" ++ showOutput (i - 4_000_000_000) n
    | i >= 1_000_000_000 && n >= 4_000_000_000
        = "i\x305" ++ showOutput (i - 1_000_000_000) n
    | i >= 1_000_000_000 = "m" ++ showOutput (i - 1_000_000_000) n
    | i >= 900_000_000   = "cm" ++ showOutput (i - 900_000_000) n
    | i >= 500_000_000   = "d" ++ showOutput (i - 500_000_000) n
    | i >= 400_000_000   = "cd" ++ showOutput (i - 400_000_000) n
    | i >= 100_000_000   = "c" ++ showOutput (i - 100_000_000) n
    | i >= 90_000_000    = "xc" ++ showOutput (i - 90_000_000) n
    | i >= 50_000_000    = "l" ++ showOutput (i - 50_000_000) n
    | i >= 40_000_000    = "xl" ++ showOutput (i - 40_000_000) n
    | i >= 10_000_000    = "x" ++ showOutput (i - 10_000_000) n
    | i >= 9_000_000     = "ix" ++ showOutput (i - 9_000_000) n
    | i >= 5_000_000     = "v" ++ showOutput (i - 5_000_000) n
    | i >= 4_000_000     = "iv" ++ showOutput (i - 4_000_000) n
    | i >= 1_000_000 && n `mod` 10_000_000 >= 4_000_000
        = "i" ++ showOutput (i - 1_000_000) n
    | i >= 1_000_000     = "M\x305" ++ showOutput (i - 1_000_000) n
    | i >= 900_000       = "C\x305" ++ "M\x305" ++ showOutput (i - 900_000) n
    | i >= 500_000       = "D\x305" ++ showOutput (i - 500_000) n
    | i >= 400_000       = "C\x305" ++ "D\x305" ++ showOutput (i - 400_000) n
    | i >= 100_000       = "C\x305" ++ showOutput (i - 100_000) n
    | i >= 90_000        = "X\x305" ++ "C\x305" ++ showOutput (i - 90_000) n
    | i >= 50_000        = "L\x305" ++ showOutput (i - 50_000) n
    | i >= 40_000        = "X\x305" ++ "L\x305" ++ showOutput (i - 40_000) n
    | i >= 10_000        = "X\x305" ++ showOutput (i - 10_000) n
    | i >= 9_000         = "I\x305" ++ "X\x305" ++ showOutput (i - 9_000) n
    | i >= 5_000         = "V\x305" ++ showOutput (i - 5_000) n
    | i >= 4_000         = "I\x305" ++ "V\x305" ++ showOutput (i - 4_000) n
    | i >= 1_000 && n `mod` 10_000 >= 4_000
        = "I\x305" ++ showOutput (i - 1_000) n
    | i >= 1_000         = "M" ++ showOutput (i - 1_000) n
    | i >= 900           = "CM" ++ showOutput (i - 900) n
    | i >= 500           = "D" ++ showOutput (i - 500) n
    | i >= 400           = "CD" ++ showOutput (i - 400) n
    | i >= 100           = "C" ++ showOutput (i - 100) n
    | i >= 90            = "XC" ++ showOutput (i - 90) n
    | i >= 50            = "L" ++ showOutput (i - 50) n
    | i >= 40            = "XL" ++ showOutput (i - 40) n
    | i >= 10            = "X" ++ showOutput (i - 10) n
    | i >= 9             = "IX" ++ showOutput (i - 9) n
    | i >= 5             = "V" ++ showOutput (i - 5) n
    | i >= 4             = "IV" ++ showOutput (i - 4) n
    | i >= 1             = "I" ++ showOutput (i - 1) n
    | otherwise          = ""

parseInputNums :: World -> Prog -> [String] -> Integer -> Either (World, Error) Integer
parseInputNums _ _ [] i = Right i
parseInputNums w p ("":s) i = parseInputNums w p s i
parseInputNums w p ("OH":s) i = parseInputNums w p s (i*10)
parseInputNums w p ("ZERO":s) i = parseInputNums w p s (i*10)
parseInputNums w p ("ONE":s) i = parseInputNums w p s (i*10+1)
parseInputNums w p ("TWO":s) i = parseInputNums w p s (i*10+2)
parseInputNums w p ("THREE":s) i = parseInputNums w p s (i*10+3)
parseInputNums w p ("FOUR":s) i = parseInputNums w p s (i*10+4)
parseInputNums w p ("FIVE":s) i = parseInputNums w p s (i*10+5)
parseInputNums w p ("SIX":s) i = parseInputNums w p s (i*10+6)
parseInputNums w p ("SEVEN":s) i = parseInputNums w p s (i*10+7)
parseInputNums w p ("EIGHT":s) i = parseInputNums w p s (i*10+8)
parseInputNums w p ("NINE":s) i = parseInputNums w p s (i*10+9)
parseInputNums w p (str:_) _ = getErrStmt w p >>= \stmt -> Left (w, Err579InvInput str stmt)

getErrStmt :: World -> Prog -> Either (World, Error) Stmt
getErrStmt w []    = Left (w, Err633ProgEnd)
getErrStmt _ (s:_) = Right s

getStack :: World -> Integer -> Either (World, Error) (World, Integer)
getStack (W v st m3 iv []) _ = Left (W v st m3 iv [], Err632TooResume)
getStack (W v st m3 iv ns) 0 = Right (W v st m3 iv ns, 0)
getStack (W v st m3 iv (n2:s)) 1 = Right (W v st m3 iv s, n2)
getStack (W v st m3 iv (_:s)) n = getStack (W v st m3 iv s) (n-1)

interpExp :: World -> Prog -> Exp -> Either (World, Error) (Integer, Bool)
interpExp (W (V m1 m2 am1 am2) st m3 iv ns) p (Var16 n) = case M.lookup n m1 of
    Just i1  -> Right (i1, False)
    Nothing -> getErrStmt (W (V m1 m2 am1 am2) st m3 iv ns) p
        >>= \stmt -> Left (W (V m1 m2 am1 am2) st m3 iv ns, Err200InvVar stmt)
interpExp (W (V m1 m2 am1 am2) st m3 iv ns) p (Var32 n) = case M.lookup n m2 of
    Just i1  -> Right (i1, True)
    Nothing -> getErrStmt (W (V m1 m2 am1 am2) st m3 iv ns) p
        >>= \stmt -> Left (W (V m1 m2 am1 am2) st m3 iv ns, Err200InvVar stmt)
interpExp w p (Array16 _) = getErrStmt w p >>= \stmt -> Left (w, Err241InvArrDim stmt)
interpExp w p (Array32 _) = getErrStmt w p >>= \stmt -> Left (w, Err241InvArrDim stmt)
interpExp w p (Const n)   = if n < 65_536
    then Right (n, False)
    else getErrStmt w p >>= \stmt -> Left (w, Err017InvConst stmt)
interpExp (W (V m1 m2 am1 am2) st m3 iv ns) p (Sub (Array16 n) el) =
    case M.lookup n am1 of
        Just arr -> interpExpList (W (V m1 m2 am1 am2) st m3 iv ns) p el
            >>= (retrieveArray (W (V m1 m2 am1 am2) st m3 iv ns) p arr
                >=> (\ m -> Right (m, False)))
        Nothing  -> getErrStmt (W (V m1 m2 am1 am2) st m3 iv ns) p
            >>= \stmt -> Left (W (V m1 m2 am1 am2) st m3 iv ns, Err200InvVar stmt)
interpExp (W (V m1 m2 am1 am2) st m3 iv ns) p (Sub (Array32 n) el) =
    case M.lookup n am2 of
        Just arr -> interpExpList (W (V m1 m2 am1 am2) st m3 iv ns) p el
            >>= (retrieveArray (W (V m1 m2 am1 am2) st m3 iv ns) p arr
                >=> (\ m -> Right (m, True)))
        Nothing  -> getErrStmt (W (V m1 m2 am1 am2) st m3 iv ns) p
            >>= \stmt -> Left (W (V m1 m2 am1 am2) st m3 iv ns, Err200InvVar stmt)
interpExp w p (Sub _ _) = getErrStmt w p >>= \stmt -> Left (w, Err200InvVar stmt)
interpExp w p (Una u e) = interpExp w p e >>= \(i, b) -> Right (interpUOp u i b, b)
interpExp w p (Bin bop e1 e2) = interpExp w p e1
    >>= \(i1, b1) -> interpExp w p e2 >>= \(i2, b2) -> interpBinOp bop b1 b2 w p i1 i2

interpUOp :: UOp -> Integer -> Bool -> Integer
interpUOp AND n False = n .&. shiftR n 16
interpUOp OR n  False = n .|. shiftR n 16
interpUOp XOR n False = n `xor` shiftR n 16
interpUOp AND n True  = n .&. shiftR n 32
interpUOp OR n  True  = n .|. shiftR n 32
interpUOp XOR n True  = n `xor` shiftR n 32

interpBinOp :: BOp -> Bool -> Bool -> World -> Prog -> Integer -> Integer -> Either (World, Error) (Integer, Bool)
interpBinOp Sel _ _ w p i1 i2         = (\i -> (i, i > 65_535)) <$> select w p i1 i2
interpBinOp Ilv b1 b2 w p i1 i2 = (, True) <$> interleave w p i1 i2 b1 b2

interleave :: World -> Prog -> Integer -> Integer -> Bool -> Bool -> Either (World, Error) Integer
interleave w p i1 i2 b1 b2
    | not b1 && not b2 = Right (convertFromBit
        (interleaveH
            (convertToBit i1 16)
            (convertToBit i2 16))
        32)
    | otherwise = getErrStmt w p >>= \stmt -> Left (w, Err275WrongSpot stmt)

interleaveH :: [Integer] -> [Integer] -> [Integer]
interleaveH [] _              = []
interleaveH _ []              = []
interleaveH (i1:il1) (i2:il2) = i1:i2:interleaveH il1 il2

select :: World -> Prog -> Integer -> Integer -> Either (World, Error) Integer
select w p i1 i2
    | i1 >= 4_294_967_296 || i2 >= 4_294_967_296 = getErrStmt w p
        >>= \stmt -> Left (w, Err533TooBig stmt)
    | otherwise = Right (convertFromBit
        (pad
            (selectH
                (convertToBit i1 32)
                (convertToBit i2 32))
            32)
        32)

selectH :: [Integer] -> [Integer] -> [Integer]
selectH [] _ = []
selectH _ [] = []
selectH (i1:il1) (1:il2) = i1:selectH il1 il2
selectH (_:il1) (_:il2) = selectH il1 il2

pad :: [Integer] -> Integer -> [Integer]
pad il = padH il il

padH :: [Integer] -> [Integer] -> Integer -> [Integer]
padH [] il2 0      = il2
padH [] il2 n      = 0:padH [] il2 (n-1)
padH (_:il1) il2 n = padH il1 il2 (n-1)

shiftR :: Integer -> Integer -> Integer
shiftR i p = ((2^(p-1))*(i `mod` 2)) + i `div` 2

convertToBit :: Integer -> Integer -> [Integer]
convertToBit i p
    | i < 0 || p <= 0 = []
    | otherwise      = (i `div` (2^(p-1))) : convertToBit (i `mod` (2^(p-1))) (p-1)

convertFromBit :: [Integer] -> Integer -> Integer
convertFromBit [] _     = 0
convertFromBit (1:il) p = (2^(p-1)) + convertFromBit il (p-1)
convertFromBit (_:il) p = convertFromBit il (p-1)


initWorld :: Mem -> World
initWorld ls =
    W
        (V M.empty M.empty M.empty M.empty)
        (S M.empty M.empty M.empty M.empty)
        ls
        (I M.empty M.empty M.empty M.empty)
        []

formatWorld :: World -> String
formatWorld (W (V m1 m2 am1 am2) (S sm1 sm2 sam1 sam2) _ _ _) = unlines
    $  ["Variables:"]
    ++ map (formatVar ".") (M.assocs m1)
    ++ map (formatVar ":") (M.assocs m2)
    ++ map (formatVar ",") (M.assocs am1)
    ++ map (formatVar ";") (M.assocs am2)
    ++ ["\nStashes:"]
    ++ map (formatVar ".") (M.assocs sm1)
    ++ map (formatVar ":") (M.assocs sm2)
    ++ map (formatVar ",") (M.assocs sam1)
    ++ map (formatVar ";") (M.assocs sam2)


formatVar :: Show a => String -> (Integer, a) -> String
formatVar pre (x,v) = pre ++ show x ++ " -> " ++ show v

showError :: Error -> String
showError e = (\(n, err, s) -> case s of
    Just stmt -> "ICL"++n++"I "++err
        ++"\n        ON THE WAY TO STATEMENT"
        ++"\n        "++stmt
        ++"\n        CORRECT SOURCE AND RESUBMIT"
    Nothing -> "ICL"++n++"I "++err
        ++"\n        CORRECT SOURCE AND RESUBMIT") (errVals e)

errVals :: Error -> (String, String, Maybe String)
errVals (Err000Undecode s1 s2) = ("000", prettyStmt s1, Just (prettyStmt s2))
errVals (Err017InvConst s) =
    ("017", "DO YOU EXPECT ME TO FIGURE THIS OUT?", Just (prettyStmt s))
errVals Err079Impolite = ("079", "PROGRAMMER IS INSUFFICIENTLY POLITE", Nothing)
errVals Err099TooPolite = ("099", "PROGRAMMER IS OVERLY POLITE", Nothing)
errVals Err123Nexting = ("123", "PROGRAM HAS DISAPPEARED INTO THE BLACK LAGOON", Nothing)
errVals Err127SysLib  =
    ("127", "SAYING 'ABRACADABRA' WITHOUT A MAGIC WAND WON'T DO YOU ANY GOOD", Nothing)
errVals Err129UndefLabel = ("129", "PROGRAM HAS GOTTEN LOST", Nothing)
errVals (Err139UndefARL s) =
    ("139", "I WASN'T PLANNING TO GO THERE ANYWAY", Just (prettyStmt s))
errVals (Err182MulLabel s) = ("182", "YOU MUST LIKE THAT LABEL A LOT!", Just (prettyStmt s))
errVals (Err197InvLabel s) =
    ("197", "SO! 65535 LABELS AREN'T ENOUGH FOR YOU?", Just (prettyStmt s))
errVals (Err200InvVar s) = ("200", "NOTHING VENTURED, NOTHING GAINED", Just (prettyStmt s))
errVals Err210InvRVar = ("200", "NOTHING VENTURED, NOTHING GAINED", Nothing)
errVals (Err240ArrDim0 s) =
    ("240", "ERROR HANDLER PRINTED SNIDE REMARK", Just (prettyStmt s))
errVals (Err241InvArrDim s) =
    ("241", "VARIABLES MAY NOT BE STORED IN WEST HYPERSPACE", Just (prettyStmt s))
errVals (Err275WrongSpot s) =
    ("275", "DON'T BYTE OFF MORE THAN YOU CAN CHEW", Just (prettyStmt s))
errVals (Err436NotStashed s) = ("436", "THROW STICK BEFORE RETRIEVING", Just (prettyStmt s))
errVals (Err533TooBig s) =
    ("533", "YOU WANT MAYBE WE SHOULD IMPLEMENT 64-BIT VARIABLES?", Just (prettyStmt s))
errVals (Err562NoInput s) = ("562", "I DO NOT COMPUTE", Just (prettyStmt s))
errVals (Err579InvInput str s) =
    ("579", "WHAT BASE AND/OR LANGUAGE INCLUDES "++str++"?", Just (prettyStmt s))
errVals (Err621E621 s) = ("621", "ERROR TYPE 621 ENCOUNTERED", Just (prettyStmt s))
errVals Err632TooResume =
    ("632", "THE NEXT STACK RUPTURES. ALL DIE. OH, THE EMBARRASSMENT!", Nothing)
errVals Err633ProgEnd = ("633", "PROGRAM FELL OFF THE EDGE", Nothing)
errVals Err774RndBug = ("774", "RANDOM COMPILER ERROR", Nothing)

prettyStmt :: Stmt -> String
prettyStmt (Cmnt _ _ str)     = rstrip str
prettyStmt (Stmt _ _ _ _ str) = rstrip str

-- https://stackoverflow.com/questions/3373327/stripping-newlines-in-haskell
rstrip :: String -> String
rstrip = reverse . dropWhile isSpace . reverse

run :: String -> Bool -> IO ()
run fileName b = do
  hSetBuffering stdout NoBuffering
  s <- readFile fileName
  case parse pIntercal "" (pWow s) of
    Left err -> putStrLn (errorBundlePretty err)
    Right p  ->
      case checkProg p of
        Left semErr      -> putStrLn (showError semErr)
        Right (_, True) -> do
            stdlibOrErr <- E.try $ readFile "stdlib.i"
            case stdlibOrErr of
                Left (_ :: IOException) -> putStrLn (showError Err127SysLib)
                Right stdlib            -> case parse pIntercal "" (pWow (s++stdlib)) of
                    Left err -> putStrLn (errorBundlePretty err)
                    Right p'  ->
                        case checkProg p' of
                            Left semErr      -> putStrLn (showError semErr)
                            Right (ls, _)    -> do
                                out <- interpProg (initWorld ls) b p' [] 0
                                case out of
                                    Right _ -> return ()
                                    Left (_, err) -> putStrLn (showError err)
        Right (ls, _) -> do
            out <- interpProg (initWorld ls) b p [] 0
            case out of
                Right _ -> return ()
                Left (_, err) -> putStrLn (showError err)

data Flags = Flags {
    filename               :: String
    , randomCompilerErrors :: Bool
    } deriving (Show, Data, Typeable)

options :: Flags
options = Flags {
    filename = def &= help "File name of Intercal program" &= typ "FILE"
    , randomCompilerErrors = True &= help "Set to False to turn off random compiler errors" &= typ "BOOL"
    } &= summary "H-Intercal"

main :: IO ()
main = do
    flags <- cmdArgs options
    case flags of
        Flags f r -> if f == ""
            then putStrLn "Please provide a file name."
            else run f r