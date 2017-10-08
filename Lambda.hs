import Type
import Parser
import Tests
import Text.ParserCombinators.Parsec
import Debug.Trace
import Data.List(nub)

tiLit (Int) = return (typeInt, [])
tiLit (Bool) = return (typeBool, [])
tiLit (LitI _) = return (typeInt, [])
tiLit (LitB _) = return (typeBool, [])

tiPat g (PVar i) = do b <- freshVar
                      return (b, g/+/[i:>:b])
tiPat g (PLit i) = do (t, s) <- tiLit i
                      return (t, g)
tiPat g (PCon i pats) = do (ts, gs') <- tiPats g pats
                           t' <- freshVar
                           let t = tiContext g i
                           let s = unify t (foldr (-->) t' ts)
                           return (apply s t', g /+/ gs')

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
                            return (t'', s5 @@ s4 @@ s3 @@ s2 @@ s1)

tiExpr g (Case e alts) = do (te, s)      <- tiExpr g e
                            fv <- freshVar
                            (t', s', g') <- tiAlts (apply s g) alts fv
                            let s'' = mapM (unify (te --> fv)) t'
                            let s''' = nub $ concat s''
                            case checkOverlap (map fst s''') of
                                Just True -> return (apply s''' fv, s''' @@ s @@ s')
                                Nothing -> error ("Error: non-unique substitutions")

checkOverlap [] = Just True
checkOverlap a@(x:xs) = case isUnique x a of
    Just True -> checkOverlap xs
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

context = [ "Just"    :>: TArr (TVar "a") (TApp (TCon "Maybe") (TVar "a")),
            "Nothing" :>: TApp (TCon "Maybe") (TVar "a"),
            "Left"    :>: TArr (TVar "a") (TApp (TApp (TCon "Either") (TVar "a")) (TVar "b")),
            "Right"   :>: TArr (TVar "b") (TApp (TApp (TCon "Either") (TVar "a")) (TVar "b")),
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
infer1 e = fst $ runTI (tiExpr context e)
hocuspocus s = do case parse start "" s of
                      Right ans -> do traceM $ "\n" ++ show ans ++ "\n"
                                      return (infer1 ans)
                      otherwise -> error ("Parse error")
