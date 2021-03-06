module Type where
import Data.List(nub, intersect, union, nubBy)
import Data.Map(fromList)

type Index = Int
type Id = String
data TI a = TI (Index -> (a, Index))
type Subst  = [(Id, SimpleType)]
data Assump = Id :>: SimpleType deriving (Eq, Show)
--data Assump = Id :>: Type deriving (Eq, Show)      {--TODO Alterar--}

data SimpleType   = TVar Id
                  | TArr SimpleType SimpleType
                  | TCon Id
                  | TApp SimpleType SimpleType
                  | TLit Lit
                  | TGen Int
                  | DCon (Id,[SimpleType])
                  deriving Eq

data Type = Forall SimpleType deriving (Eq, Show)

data Lit   = Int
           | Bool
           | LitI Int
           | LitB Bool
           deriving (Eq, Show)

data Pat = PVar Id
         | PLit Lit
         | PCon Id [Pat]
         deriving (Show, Eq)

data Expr = Var    Id
          | App    Expr Expr
          | Lam    Id Expr
          | If     Expr Expr Expr
          | Lit    Lit
          | Case   Expr [(Pat, Expr)]
          | Let    (Id, Expr) Expr   -- Numa situação real seria [(Id, Expr)]
          deriving (Eq, Show)


typeInt, typeBool :: SimpleType
typeInt  = TCon "Int"
typeBool = TCon "Bool"

instance Show SimpleType where
   show (TVar i) = i
   show (TArr a@(TArr _ _) t'') = "("++show a++")"++"->"++show t''
   show (TArr t t') = show t++"->"++show t'
   show (TApp t t') = show t ++ " " ++ show t'
   show (TCon u) = u
   show (TLit u) = show u
   show (DCon a@(u, t)) = show u ++ show t

--------------------------
instance Functor TI where
   fmap f (TI m) = TI (\e -> let (a, e') = m e in (f a, e'))

instance Applicative TI where
   pure a = TI (\e -> (a, e))
   TI fs <*> TI vs = TI (\e -> let (f, e') = fs e; (a, e'') = vs e' in (f a, e''))

instance Monad TI where
   return x = TI (\e -> (x, e))
   TI m >>= f  = TI (\e -> let (a, e') = m e; TI fa = f a in fa e')

freshVar :: TI SimpleType
freshVar = TI (\e -> let v = "t"++show e in (TVar v, e+1))

runTI (TI m) = let (t, _) = m 0 in t
----------------------------
t --> t' = TArr t t'
t |-> t' = TApp t t'

infixr 4 @@
(@@)       :: Subst -> Subst -> Subst
s1 @@ s2    = [ (u, apply s1 t) | (u,t) <- s2 ] ++ s1

tEq (x:>:y) (u:>:v) = (x == u)
idEq (a,b) (x,y) = (a == x)

(/+/)      :: [Assump] -> [Assump] -> [Assump]
a1 /+/ a2    = nubBy tEq $ reverse $ a1 `union` a2
----------------------------
class Subs t where
  apply :: Subst -> t -> t
  tv    :: t -> [Id]

instance Subs SimpleType where
  apply s (TVar u)  =
                    case lookup u s of
                       Just t  -> t
                       Nothing -> TVar u
  apply s (TCon u)  =
                    case lookup u s of
                       Just t  -> t
                       Nothing -> TCon u
  apply s (TArr l r) =  (TArr (apply s l) (apply s r))
  apply s (TApp l r) =  (TApp (apply s l) (apply s r))
  apply _ (TLit u)    = TLit u


  tv (TVar u)  = [u]
  tv (TLit u)  = []
  tv (TCon u)  = [u]
  tv (TApp l r) = tv l `union` tv r
  tv (TArr l r) = tv l `union` tv r


instance Subs a => Subs [a] where
  apply s     = map (apply s)
  tv          = nub . concat . map tv

instance Subs Assump where
  apply s (i:>:t) = i:>:apply s t
  tv (i:>:t) = tv t

------------------------------------
varBind :: Id -> SimpleType -> Maybe Subst
varBind u t | t == TVar u   = Just []
            | u `elem` tv t = Nothing
            | otherwise     = Just [(u, t)]

mgu (TArr l r,  TArr l' r') = do s1 <- mgu (l,l')
                                 s2 <- mgu ((apply s1 r) ,  (apply s1 r'))
                                 return (s2 @@ s1)
mgu ((TApp l r),(TApp l' r')) = do s1 <- mgu (l, l')
                                   s2 <- mgu ((apply s1 r),   (apply s1 r'))
                                   return (s2 @@ s1)
mgu (t,        TVar u   )   =  varBind u t
mgu (TVar u,   t        )   =  varBind u t
mgu (TCon u,   TCon t   )   |  u == t = (Just [])
                            |  otherwise = Nothing
mgu (TCon u,   t        )   =  varBind u t
mgu (t     ,   TCon u   )   =  varBind u t
mgu (TLit u,   TLit t   )   | u == t || checkLit u t = (Just [])
                            | otherwise = Nothing
mgu (_,        _        )   =  Nothing

unify t t' =  case mgu (t,t') of
    Nothing -> error ("unification: trying to unify\n" ++ (show t) ++ "\nand\n" ++
                      (show t'))
    Just s  -> s

checkLit Bool (LitB _) = True
checkLit Int (LitI _)  = True
checkLit _ _           = False

quantify vs qt = (apply s qt)
    where
        vs' = [ v | v <- tv qt, v `elem` vs]
        s = zip vs' (map TGen [0..])

inst g t = do
    g' <- mapM (const freshVar) g
    let s = zip g g'
    return (apply s t)
