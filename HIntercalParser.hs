module HIntercalParser where

import Data.Void ( Void )
import Control.Monad ( void, join )
import           Text.Megaparsec as P
import           Text.Megaparsec.Char ( space1, string )
import qualified Text.Megaparsec.Char.Lexer as L
import           Control.Monad.Combinators.Expr
    ( makeExprParser, Operator(InfixN) )
import           Data.Set (empty)
import           HIntercalTypes

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