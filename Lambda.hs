import Type
import Parser
import Tests
import Text.ParserCombinators.Parsec
import Debug.Trace
import Data.List(nub, nubBy)
import System.IO
import Control.Monad
import qualified Data.Map as Map

tiLit (Int) = return (typeInt, [])
tiLit (Bool) = return (typeBool, [])
tiLit (LitI _) = return (typeInt, [])
tiLit (LitB _) = return (typeBool, [])

tiPat g (PVar i) = do b <- freshVar
                      return (b, g++[i:>:b])
tiPat g (PLit i) = do (t, s) <- tiLit i
                      return (t, g)
tiPat g (PCon i pats) = do (ts, gs') <- tiPats g pats
                           t' <- freshVar
                           t <- tiContext g i
                           let s = unify t (foldr (-->) t' ts)
                           return (apply s t', g /+/ gs')

tiPats g pats = do pss <- mapM (tiPat g) pats
                   let ts = concat [ [ts'] | (ts',_) <- pss ]
                       gs = concat [  gs'  | (_,gs') <- pss ]
                   return (ts, gs)

tiAlt g (pat, e) = do (t', s) <- tiExpr g e
                      (t, g') <- tiPats (apply s g) [pat]
                      return (foldr (-->) t' t, s, (g /+/ g'))

tiAlts g alts    = do pss <- mapM (tiAlt g) alts
                      let ts = concat [ [ts'] | (ts',_,_) <- pss]
                          ss = concat [  ss'  | (_,ss',_) <- pss]
                          gs = concat [  gs'  | (_,_,gs') <- pss]
                      return (ts, ss, g/+/gs)

-- tiContext g i = let (_ :>: t) = head (dropWhile (\(i' :>: _) -> i /= i' ) g) in t
tiContext g i = do
    case contextLookup g i of
        Nothing -> error ("Unbound variable " ++ show i)
        Just s  -> do t <- inst (getIds g) s
                      return t

contextLookup []            i = Nothing
contextLookup (i' :>: t:xs) i = if i == i' then Just t else contextLookup xs i

tiExpr g (Var i) = do t <- tiContext g i
                      return (t, [])
tiExpr g (App e e') = do (t,  s1) <- tiExpr g e
                         (t', s2) <- tiExpr (apply s1 g) e'
                         b        <- freshVar
                         let  s3   = unify (apply s2 t) (t' --> b)
                         return (apply s3 b, s3 @@ s2 @@ s1)
tiExpr g (Lam i e) = do b <- freshVar
                        (t, s)  <- tiExpr (g /+/ [i:>:b]) e
                        --traceM $ show s
                        return (apply s (b --> t), s)
tiExpr g (Lit i) = do (t, s) <- tiLit i
                      return (t, s)
tiExpr g (If e e' e'') = do (t,   s1) <- tiExpr g e
                            (t',  s2) <- tiExpr (apply s1 g) e'
                            (t'', s3) <- tiExpr (apply s2 g) e''
                            let   s4   = unify t typeBool
                                  s5   = unify t' t''
                            return (t'', s5 @@ s4 @@ s3 @@ s2 @@ s1)

tiExpr g (Case e alts) = do (te, s)      <- tiExpr g e
                            fv           <- freshVar
                            (t', s', g') <- tiAlts (apply s g) alts
                            --let s''       = nub $ concatMap (unify (te --> fv)) t'
                            let s''       = unifyAll (te --> fv) t' []
                            let sr        = s'' @@ s' @@ s
                            -- traceM $ show g
                            return (apply sr fv, sr)
                            -- case checkOverlap (map fst s'') of
                            --      Just True -> return (apply s'' fv, s'' @@ s' @@ s)
                            --      Nothing -> error ("Error: non-unique substitutions")

tiExpr g (Let (x,e) e') = do (t, s) <- tiExpr g e
                             let g'  = apply s g
                                 t'  = quantify (getIds g') t
                             --traceM $ show t'
                             (t'', s') <- tiExpr (g' /+/ [x:>:t']) e'
                             --traceM $ show g'
                             return (t'', s' @@ s)

unifyAll t []     s = s
unifyAll t (x:xs) s = let u = unify t x
                          s'= s @@ u
                      in unifyAll (apply s' t) xs s'

getIds []             = []
getIds ((i :>: t):xs) = i : getIds xs

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

{--Fazer forall Just... --}
context = [ "+"       :>: TArr (TLit Int) (TArr (TLit Int) (TLit Int)),
            "-"       :>: TArr (TLit Int) (TArr (TLit Int) (TLit Int)),
            "*"       :>: TArr (TLit Int) (TArr (TLit Int) (TLit Int)),
            "/"       :>: TArr (TLit Int) (TArr (TLit Int) (TLit Int)),
            "=="      :>: TArr (TLit Int) (TArr (TLit Int) (TLit Bool)),
            ">"       :>: TArr (TLit Int) (TArr (TLit Int) (TLit Bool)),
            ">="      :>: TArr (TLit Int) (TArr (TLit Int) (TLit Bool)),
            "<"       :>: TArr (TLit Int) (TArr (TLit Int) (TLit Bool)),
            "<="      :>: TArr (TLit Int) (TArr (TLit Int) (TLit Bool))]

getContext = do content <- readFile "typeDecl.txt"
                return $ context ++ ([content] >>= getAssumps . init . lines)
                where
                    getAssumps [] = []
                    getAssumps (x:xs) =
                        case parse startData "" x of
                            Right ans -> ans ++ getAssumps xs
                            Left  err -> error $ "Type declaration error at" ++ show x

infer e = runTI (tiExpr context e)
infer1 e g = fst $ runTI (tiExpr g e)

main = do content <- readFile "typeDecl.txt"
          hocuspocus $ [content] >>= last . lines

hocuspocus s = case parse start "" s of
                Right ans -> do g <- getContext
                                traceM $ "\n" ++ show ans ++ "\n"
                                return (infer1 ans g)
                Left  err -> error ("Parse error")
