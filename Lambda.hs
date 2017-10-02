import Type
import Debug.Trace

data Expr    =  Var     Id
             | App    Expr Expr
             | Lam    Id Expr
             | If     Expr Expr Expr
             | Lit    Lit
             | Case   Expr [(Pat, Expr)]
             | Op     BinOp Expr Expr
             deriving (Eq, Show)

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
                      return (ts, ss, gs)


tiContext g i = let (_ :>: t) = head (dropWhile (\(i' :>: _) -> i /= i' ) g) in t

tiExpr g (Var i) = return (tiContext g i, [])
tiExpr g (App e e') = do (t, s1) <- tiExpr g e
                         (t', s2) <- tiExpr (apply s1 g) e'
                         b <- freshVar
                         let s3 = unify (apply s2 t) (t' --> b)
                         return (apply s3 b, s3 @@ s2 @@ s1)
tiExpr g (Lam i e) = do b <- freshVar
                        (t, s)  <- tiExpr (g /+/ [i:>:b]) e
                        traceM $ show s
                        traceM $ show (g ++[i:>:b])
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
                            [(t', s', g')] <- mapM (tiAlt (apply se g)) alts

                            traceM $ "alts: " ++ show t'
                            traceM $ "alts subs: " ++ show s'
                            traceM $ "alts env: " ++ show g'
                            traceM $ "expr type: " ++ show te
                            traceM $ "expr subs: " ++ show se
                            let s'' = unify te t'
                            traceM $ "s'' = " ++ show s''
                            traceM $ "apply: " ++ show (apply s'' te)
                            return (apply s'' te, [])

tiExpr g (Op op e e') = do (t1, s1) <- tiExpr g e
                           (t2, s2) <- tiExpr g e
                           fv <- freshVar
                           traceM $ "freshVar: " ++ show fv
                           let s3    = unify (t1 --> (t2 --> fv)) (getOp op)
                           traceM $ "s3: " ++ show s3
                           --let u = unify (t1 --> t2) (getOp op)
                           return (apply s3 fv, s1 @@ s2 @@ s3)

getOp op = case op of
                Add -> ((typeInt --> (typeInt --> typeInt)))
                Sub -> ((typeInt --> (typeInt --> typeInt)))
                Mul -> ((typeInt --> (typeInt --> typeInt)))
                Div -> ((typeInt --> (typeInt --> typeInt)))
                Eql -> ((typeInt --> (typeInt --> typeBool)))



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
-- excase = Lam "x" (Case (Var "x") [((PCon "Just" [Var "x"]), (Var "x")))
ex1case = Lam "x" (Case (Var "x") [((PCon "Just" [PVar "x"]), (Lit (LitB True))), (PCon "Nothing" [], Lit (LitB False))])
ex2case = Lam "x" (Case (Var "x") [(PLit (LitB True), (Var "x"))])
ex3case = Lam "x" (Case (Var "x") [((PCon "Just" [PVar "x"]), (Lit (LitB True)))])


-- Bin Ops --
suc = Lam "x" (Op Add (Var "x") (Lit (LitI 1)))
add = Lam "x" (Lam "y" (Op Add (Var "x") (Var "y")))
eq  = Lam "x" (Lam "y" (Op Eql (Var "x") (Var "y")))



contexto = ["Just" :>: TArr (TVar "a") (TApp (TCon "Maybe") (TVar "a")),
            "Nothing" :>: TApp (TCon "Maybe") (TVar "a")]

infer e = runTI (tiExpr contexto e)




mycase x = case x of
    Just x -> True

othercase = (\x -> case x of
                        Just x -> True)

-- tiExpr g (Case e alts) = do (ts, ss, gs) <- tiAlts g alts
--                             (te, se)     <- tiExpr (g /+/ gs) e
--                             t' <- freshVar
--                             let s''       = unify te (foldr (-->) t' ts)
--                             return (apply s'' te, s'' @@ se)
