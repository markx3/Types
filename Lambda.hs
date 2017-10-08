import Type
import Debug.Trace

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
                      return (foldr (-->) t' t, s, (g' /+/ g))

tiAlts g alts    = do pss <- mapM (tiAlt g) alts
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
                        traceM $ show s ++ "\n"
                        traceM $ show (g ++[i:>:b]) ++ "\n"
                        return (apply s (b --> t), s)
tiExpr g (Lit i) = do (t, s) <- tiLit i
                      return (t, s)
tiExpr g (If e e' e'') = do (t,   s1) <- tiExpr g e
                            (t',  s2) <- tiExpr (apply s1 g) e'
                            (t'', s3) <- tiExpr (apply s2 g) e''
                            let s4 = unify t typeBool
                                s5 = unify t' t''
                            -- traceM $ show (s5)
                            return (apply s5 t'', s5 @@ s4 @@ s3 @@ s2 @@ s1)

tiExpr g (Case e alts) = do (te, se)     <- tiExpr g e
                            (t', s', g') <- tiAlts (apply se g) alts
                            -- traceM $ "alts: " ++ show t'
                            -- traceM $ "alts subs: " ++ show s'
                            -- traceM $ "alts env: " ++ show g'
                            -- traceM $ "expr type: " ++ show te
                            -- traceM $ "expr subs: " ++ show se
                            fv <- freshVar
                            let s'' = unify' fv t'
                                s''' = s' @@ s'' @@ se

                            traceM $ "s'' = " ++ show s''
                            --traceM $ "s'' = " ++ show s''
                            --traceM $ "apply: " ++ show (apply s'' te)
                            return (fv, s''' @@ (nullSubst te))

unify' t [x] = unify t x
unify' t (x:xs) = let s = unify t x in unify' (apply s t) xs

-- unify'' t [x]     = unify t x
-- unify'' t (x:xs) = let s = unify t x in unify' (apply s t) xs

appParametros i [] = i
appParametros (TArr a i) (t:ts) = appParametros i ts

-- tiExpr g (Case e alts) = do (te, se)     <- tiExpr g e
--                             (t', s', g') <- tiAlts g alts
--
--                             traceM $ "alts: " ++ show t'
--                             traceM $ "alts subs: " ++ show s'
--                             traceM $ "alts env: " ++ show g'
--                             traceM $ "expr type: " ++ show te
--                             traceM $ "expr subs: " ++ show se
--                             let s'' = foldr unify te t'
--                             traceM $ "s'' = " ++ show s''
--                             traceM $ "apply: " ++ show (apply s'' te)
--                             return (apply s'' te, [])



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

-- excase = Lam "x" (Case (Var "x") [((PCon "Just" [Var "x"]), (Var "x")))
ex1case = Lam "x" (Case (Var "x") [((PCon "Just" [PVar "x"]), (Lit (LitB True))), (PCon "Nothing" [], Lit (LitB False))])
ex2case = Lam "x" (Case (Var "x") [(PLit (LitB True), (Lit (LitI 1)))])
ex3case = Lam "x" (Case (Var "x") [((PCon "Just" [PVar "x"]), (Lit (LitB True)))])


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




mycase x = case x of
    Just x -> True

othercase = (\x -> case x of
                        Just x -> True)

-- tiExpr g (Case e alts) = do (ts, ss, gs) <- tiAlts g alts
--                             (te, se)     <- tiExpr (g /+/ gs) e
--                             t' <- freshVar
--                             let s''       = unify te (foldr (-->) t' ts)
--                             return (apply s'' te, s'' @@ se)
