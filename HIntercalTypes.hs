{-# Language GADTSyntax #-}

module HIntercalTypes where

import qualified Data.Map as M

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

{- | `Mem` is a map of `Integer` keys to `Integer` values. It is used to keep track of
the relation between labels and line names, as well as the value of variables (which all
have `Integer` names).
-}
type Mem = M.Map Integer Integer

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