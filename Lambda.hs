import Type

data Lit     = LitI Integer
             | LitB Bool
             deriving (Eq, Show, Ord)

data Expr    =  Var     Id
             | App    Expr Expr
             | Lam    Id Expr
             | If     Expr Expr Expr
             | Lit    Lit
             deriving (Eq, Show)


tiContext g i = let (_ :>: t) = head (dropWhile (\(i' :>: _) -> i /= i' ) g) in t

tiExpr g (Var i) = return (tiContext g i, [])
tiExpr g (App e e') = do (t, s1) <- tiExpr g e
                         (t', s2) <- tiExpr (apply s1 g) e'
                         b <- freshVar
                         let s3 = unify (apply s2 t) (t' --> b)
                         return (apply s3 b, s3 @@ s2 @@ s1)
tiExpr g (Lam i e) = do b <- freshVar
                        (t, s)  <- tiExpr (g++[i:>:b]) e
                        return (apply s (b --> t), s)
tiExpr g (If e e' e'') = do (t, s1) <- tiExpr g e
                            (t', s2) <- tiExpr g e'
                            (t'', s3) <- tiExpr g e''
                            let s4 = unify t typeBool
                                s5 = unify t' t''
                            ---let s4 = unify (apply s2 t'') (apply s3 t')
                            return (apply s5 t'',s5 @@ s4 @@ s3 @@ s2 @@ s1)


ex1 = Lam "f" (Lam "x" (App (Var "f") (Var "x")))
ex2 = Lam "x" (App (Var "x") (Var "x"))
ex3 = Lam "g" (Lam "f" (Lam "x" (App (Var "g") (App (Var "f") (Var "x")))))
ex4 = If ex1 ex3 ex3
infer e = runTI (tiExpr [] e)
