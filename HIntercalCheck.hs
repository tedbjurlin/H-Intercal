{-# LANGUAGE NumericUnderscores #-}

module HIntercalCheck where

import qualified Data.Map as M
import           HIntercalTypes

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