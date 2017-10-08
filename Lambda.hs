import Type
import Debug.Trace
import Data.List(nub)

data Expr    =  Var     Id
             | App    Expr Expr
             | Lam    Id Expr
             | If     Expr Expr Expr
             | Lit    Lit
             | Case   Expr [(Pat, Expr)]
             deriving (Eq, Show)

tiLit (Int) = return (typeInt, [])
tiLit (Bool) = return (typeBool, [])
tiLit (LitI _) = return (typeInt, [])
tiLit (LitB _) = return (typeBool, [])

tiPat g (PVar i) = do let b = tiContext g i
                      return (b, g/+/[i:>:b])
tiPat g (PLit i) = do (t, s) <- tiLit i
                      return (t, g)
tiPat g (PCon i pats) = do (ts, gs') <- tiPats g pats
                           t' <- freshVar
                           let t = tiContext g i
                           let s = unify t (foldr (-->) t' ts)
                           return (apply s t', gs'/+/g)

tiPats g pats = do pss <- mapM (tiPat g) pats
                   let ts = concat [ [ts'] | (ts',_) <- pss ]
                       gs = concat [  gs'  | (_,gs') <- pss ]
                   return (ts, gs)

tiAlt g (pat, e) = do (t', s) <- tiExpr g e
                      (t, g') <- tiPats (apply s g) [pat]
                      return (foldr (-->) t' t, s, (g /+/ g'))

tiAlts g alts t  = do pss <- mapM (tiAlt g) alts
                      let ts = concat [ [ts'] | (ts',_,_) <- pss]
                          ss = concat [  ss'  | (_,ss',_) <- pss]
                          gs = concat [  gs'  | (_,_,gs') <- pss]
                      return (ts, ss, g/+/gs)

tiContext g i = let (_ :>: t) = head (dropWhile (\(i' :>: _) -> i /= i' ) g) in t

tiExpr g (Var i) = return (tiContext g i, [])
tiExpr g (App e e') = do (t, s1) <- tiExpr g e
                         (t', s2) <- tiExpr (apply s1 g) e'
                         b <- freshVar
                         let s3 = unify (apply s2 t) (t' --> b)
                         return (apply s3 b, s3 @@ s2 @@ s1)
tiExpr g (Lam i e) = do b <- freshVar
                        (t, s)  <- tiExpr (g /+/ [i:>:b]) e
                        return (apply s (b --> t), s)
tiExpr g (Lit i) = do (t, s) <- tiLit i
                      return (t, s)
tiExpr g (If e e' e'') = do (t,   s1) <- tiExpr g e
                            (t',  s2) <- tiExpr (apply s1 g) e'
                            (t'', s3) <- tiExpr (apply s2 g) e''
                            let s4 = unify t typeBool
                                s5 = unify t' t''
                            return (apply s5 t'', s5 @@ s4 @@ s3 @@ s2 @@ s1)

tiExpr g (Case e alts) = do (te, s)      <- tiExpr g e
                            (t', s', g') <- tiAlts (apply s g) alts te
                            fv <- freshVar
                            let s'' = map (unify (te --> fv)) t'
                                s''' = nub $ concat s''

                            case findRepeated (map fst s''') of
                                Just True -> return (apply s''' fv, s''' @@ s @@ s')
                                Nothing -> error ("oops")

findRepeated [] = Just True
findRepeated a@(x:xs) = case isUnique x a of
    Just True -> findRepeated xs
    otherwise -> Nothing

isUnique :: Eq a => a -> [a] -> Maybe Bool
isUnique a = go Nothing a
    where go s _ [] = s
          go s@Nothing x (z:zs)
            | x == z = go (Just True) x zs
            | otherwise = go s x zs
          go s@(Just True) x (z:zs)
            | x == z = Just False
            | otherwise = go s x zs
          go s@(Just False) _ _ = s


ex1 = Lam "f" (Lam "x" (App (Var "f") (Var "x")))
ex2 = Lam "x" (App (Var "x") (Var "x"))
ex3 = Lam "g" (Lam "f" (Lam "x" (App (Var "g") (App (Var "f") (Var "x")))))
true = Lit (LitB True)
ex4 = If (Lit (LitB False)) (Lit (LitI 10)) (App (Lam "x" (Var "x")) (Lit (LitI 20)))
ex5 = Lit (LitI 2)
-- ((\x.x)(\y.y))(True)
ex6 = ((App (App (Lam "x" (Var "x")) (Lam "y" (Var "y"))) (Lit (LitB True))))
ex7 = (App (Lam "x" (Var "x")) (If (Lit (LitB True)) (Lit (LitI 10)) (Lit (LitI 20))))
ex8 = (App (If (Lit (LitB True)) (Lit (LitI 10)) (Lit (LitI 20))) (Lam "x" (Var "x")))
exif = Lam "x" (If (Var "x") (Lit (LitI 1)) (Lit (LitI 0)))
exif2 = Lam "x" (Lam "y" (If (Var "x") (Var "y") (Lit (LitI 0))))
exif3 = Lam "x" (Lam "y" (Lam "z" (If (Var "x") (Var "y") (Var "z"))))
exif4 = Lam "x" (Lam "y" (If (App (App (Var "==") (Var "x")) (Var "y")) (Var "x") (Var "y")))

-- Case Examples --
ex1case = Lam "x" (Case (Var "x") [((PCon "Just" [PVar "x"]), (Lit (LitB True))), (PCon "Nothing" [], Lit (LitB False))])
ex2case = Lam "x" (Case (Var "x") [(PLit (LitB True), (Lit (LitI 1)))])
ex3case = Lam "x" (Case (Var "x") [((PCon "Just" [PVar "x"]), (Lit (LitB True)))])
ex4case = Lam "x" (Case (Var "x") [(PLit (LitI 1), Lit (LitB True)), (PLit (LitI 2), Lit (LitB True)), (PLit (LitI 0), Lit (LitB False))])

-- Shouldn't work
ex5case = Lam "x" (Case (Var "x") [((PCon "Just" [PVar "x"], (Lit (LitB True)))), ((PCon "Nothing" [], Lit (LitI 1)))])

-- Bin Ops --
suc = Lam "x" (App (App (Var "+") (Var "x")) (Lit (LitI 1)))
add = Lam "x" (Lam "y" (App (App (Var "+") (Var "x")) (Var "y")))

context = [ "Just"    :>: TArr (TVar "a") (TApp (TCon "Maybe") (TVar "a")),
            "Nothing" :>: TApp (TCon "Maybe") (TVar "a"),
            "+"       :>: TArr (TLit Int) (TArr (TLit Int) (TLit Int)),
            "-"       :>: TArr (TLit Int) (TArr (TLit Int) (TLit Int)),
            "*"       :>: TArr (TLit Int) (TArr (TLit Int) (TLit Int)),
            "/"       :>: TArr (TLit Int) (TArr (TLit Int) (TLit Int)),
            "=="      :>: TArr (TLit Int) (TArr (TLit Int) (TLit Bool)),
            ">"       :>: TArr (TLit Int) (TArr (TLit Int) (TLit Bool)),
            ">="      :>: TArr (TLit Int) (TArr (TLit Int) (TLit Bool)),
            "<"       :>: TArr (TLit Int) (TArr (TLit Int) (TLit Bool)),
            "<="      :>: TArr (TLit Int) (TArr (TLit Int) (TLit Bool))]

infer e = runTI (tiExpr context e)
