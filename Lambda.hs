import Type
import Debug.Trace

data Expr    =  Var     Id
             | App    Expr Expr
             | Lam    Id Expr
             | If     Expr Expr Expr
             | Lit    Lit
             | Case   Expr [(Pat, Expr)]
             deriving (Eq, Show)

tiLit (LitI _) = return (typeInt, [])
tiLit (LitB _) = return (typeBool, [])

tiPat g (PVar i) = do b <- freshVar
                      return (b, g/+/[i:>:b])
tiPat g (PLit i) = do (t, s) <- tiLit i
                      return (t, g)
tiPat g (PCon i pats) = do (ts, gs') <- tiPats g pats
                           t' <- freshVar
                           let t = freshInst i
                           traceM $ show ts
                           traceM $ show gs'
                           let s = unify t (foldr (-->) t' ts)
                           return (apply s t', gs'/+/g)

tiPats g pats = do pss <- mapM (tiPat g) pats
                   let ts = concat [ [ts'] | (ts',_) <- pss ] {--Criar lista de tipos a partir da dupla--}
                       gs = concat [ gs' | (_,gs') <- pss ]   {--Criar lista de environments a partir da dupla--}
                   traceM $ show ts
                   traceM $ show gs
                   return (ts, gs)

tiAlt g (pat, e) = do (t, g') <- tiPats g [pat]
                      (t', s) <- tiExpr (g' /+/ g) e
                      return (foldr (-->) t' t, s, (g' /+/ g))

-- tiAlts g alts = do (ts, gs) <- mapM (tiAlt g) alts
--                    let s = unify

tiContext g i = let (_ :>: t) = head (dropWhile (\(i' :>: _) -> i /= i' ) g) in t

tiExpr g (Var i) = return (tiContext g i, [])
tiExpr g (App e e') = do (t, s1) <- tiExpr g e
                         (t', s2) <- tiExpr (apply s1 g) e'
                         b <- freshVar
                         let s3 = unify (apply s2 t) (t' --> b)
                         return (apply s3 b, s3 @@ s2 @@ s1)
tiExpr g (Lam i e) = do b <- freshVar
                        (t, s)  <- tiExpr (g/+/[i:>:b]) e -- Arrumar p/ verificar se existe variavel com esse nome (/+/ p/ excluir)
                        return (apply s (b --> t), s)    {-- primeiro verifica se existe, tira dps adiciona nova variave --}
tiExpr g (Lit i) = do (t, s) <- tiLit i
                      return (t, s)
tiExpr g (If e e' e'') = do (t,   s1) <- tiExpr g e
                            (t',  s2) <- tiExpr g e'
                            (t'', s3) <- tiExpr g e''
                            let s4 = unify t typeBool
                                s5 = unify t' t''
                            -- traceM $ show (s5)
                            return (apply s5 t'', s5 @@ s4 @@ s3 @@ s2 @@ s1)
-- tiExpr g (Case e pats) = do (

tiExpr g (Case e pats) = do [(t', s', g')] <- mapM (tiAlt g) pats
                            (te, se)     <- tiExpr (g/+/g') e
                            let s'' = unify t' te
                            return (apply s'' te, s'' @@ s')

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
-- excase = Lam "x" (Case (Var "x") [((PCon "Just" [Var "x"]), (Var "x")))
ex1case = Lam "x" (Case (Var "x") [((PCon "Just" [PVar "y"]), (Lit (LitB True))), (PCon "Nothing" [], Lit (LitB False))])
ex2case = Lam "x" (Case (Var "x") [(PVar "x", Lit (LitI 1))])

infer e = runTI (tiExpr [] e)
