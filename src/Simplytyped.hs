module Simplytyped
  ( conversion
  ,    -- conversion a terminos localmente sin nombre
    eval
  ,          -- evaluador
    infer
  ,         -- inferidor de tipos
    quote          -- valores -> terminos
  )
where

import           Data.List
import           Data.Maybe
import           Prelude                 hiding ( (>>=) )
import           Text.PrettyPrint.HughesPJ      ( render )
import           PrettyPrinter
import           Common
import           Data.Map.Strict         as M

-----------------------
-- conversion
-----------------------

-- conversion a términos localmente sin nombres
conversion :: LamTerm -> Term
conversion = conversionAux (M.empty)  


type BoundedVars = M.Map String Int


conversionAux :: BoundedVars -> LamTerm -> Term
conversionAux idxs (LVar x)           = case M.lookup x idxs of 
                                          Nothing -> Free (Global x)
                                          Just i  -> Bound i

conversionAux idxs (LApp lt1 lt2)     = (conversionAux idxs lt1 ) :@: 
                                        (conversionAux idxs lt2 )  

conversionAux idxs (LAbs x t lt)      = let
                                          idxs'  = M.map succ idxs
                                          idxs'' = M.insert x 0 idxs'
                                        in Lam t (conversionAux idxs'' lt) 

conversionAux idxs (LLet x lt1 lt2)   = let 
                                          idxs'  = M.map succ idxs
                                          idxs'' = M.insert x 0 idxs' 
                                        in
                                          Let (conversionAux idxs lt1) (conversionAux idxs'' lt2)  

conversionAux idxs (LZero)            = Zero
conversionAux idxs (LSuc t)           = Suc (conversionAux idxs t)
conversionAux idxs (LRec t1 t2 t3)    = Rec t1' t2' t3' 
                                        where 
                                          t1' = conversionAux idxs t1 
                                          t2' = conversionAux idxs t2 
                                          t3' = conversionAux idxs t3 

conversionAux idxs LNil               = Nil
conversionAux idxs (LCons t1 t2)      = Cons (conversionAux idxs t1) (conversionAux idxs t2)
conversionAux idxs (LRecL t1 t2 t3)   = RecL t1' t2' t3'
                                        where
                                          t1' = conversionAux idxs t1 
                                          t2' = conversionAux idxs t2 
                                          t3' = conversionAux idxs t3 

----------------------------

--- evaluador de términos
----------------------------

-- substituye una variable por un término en otro término
sub :: Int -> Term -> Term -> Term
sub i t (Bound j) | i == j    = t
sub _ _ (Bound j) | otherwise = Bound j
sub _ _ (Free n   )           = Free n
sub i t (u   :@: v)           = sub i t u :@: sub i t v
sub i t (Lam t'  u)           = Lam t' (sub (i + 1) t u)
sub i t (Let t1  t2)          = Let (sub i t t1) (sub (i + 1) t t2) 
sub _ _ Zero                  = Zero 
sub i t (Suc t')              = Suc (sub i t t')
sub i t (Rec t1 t2 t3)        = Rec (sub i t t1) (sub i t t2) (sub i t t3)
sub _ _ Nil                   = Nil
sub i t (Cons t1 t2)          = Cons (sub i t t1) (sub i t t2)
sub i t (RecL t1 t2 t3)       = RecL (sub i t t1) (sub i t t2) (sub i t t3)

quote :: Value -> Term
quote (VLam t f) = Lam t f
quote (VNum nv)  = quoteN nv
quote (VList lv) = quoteL lv

quoteN :: NumVal -> Term
quoteN NZero     = Zero
quoteN (NSuc nv) = Suc $ quoteN nv

quoteL :: ListVal -> Term
quoteL VNil          = Nil
quoteL (VCons nv lv) = Cons (quoteN nv) (quoteL lv) 


-- evalúa un término en un entorno dado
eval :: NameEnv Value Type -> Term -> Value
eval _ (Bound j)        = error "error: evaluating bounded variable"
eval ne (Free x)        = case Prelude.lookup x ne of
                            Nothing     -> error "error: variable not in name enviroment"
                            Just (v, t) -> v 

eval _ (Lam t f  )      = VLam t f

eval ne (t1 :@: t2)     = let
                            (Lam t f) = quote (eval ne t1)
                            t2'       = quote (eval ne t2)
                            tsub      = sub 0 t2' f 
                          in eval ne tsub

eval ne (Let t1 t2)     = let
                            t1'  = quote (eval ne t1)
                            tsub = sub 0 t1' t2
                          in
                            eval ne tsub

eval _ Zero             = VNum NZero
eval ne (Suc t)         = VNum (NSuc n) where (VNum n) = eval ne t
eval ne (Rec t1 t2 t3)  = case eval ne t3 of
                            VNum NZero     -> eval ne t1
                            VNum (NSuc nv) -> eval ne (t2 :@: Rec t1 t2 t :@: t) 
                                              where t = quoteN nv

eval _ Nil              = VList VNil
eval ne (Cons t1 t2)    = let
                            (VNum n)   = eval ne t1
                            (VList lv) = eval ne t2
                          in VList (VCons n lv)

eval ne (RecL t1 t2 t3) = case eval ne t3 of
                             VList VNil          -> eval ne t1
                             VList (VCons nv lv) -> eval ne (t2 :@: tn :@: tl :@: RecL t1 t2 tl)
                                                    where tn = quoteN nv
                                                          tl = quoteL lv

----------------------
--- type checker
-----------------------

-- infiere el tipo de un término
infer :: NameEnv Value Type -> Term -> Either String Type
infer = infer' []

-- definiciones auxiliares
ret :: Type -> Either String Type
ret = Right

err :: String -> Either String Type
err = Left

(>>=)
  :: Either String Type -> (Type -> Either String Type) -> Either String Type
(>>=) v f = either Left f v
-- fcs. de error

matchError :: Type -> Type -> Either String Type
matchError t1 t2 =
  err
    $  "se esperaba "
    ++ render (printType t1)
    ++ ", pero "
    ++ render (printType t2)
    ++ " fue inferido."

notfunError :: Type -> Either String Type
notfunError t1 = err $ render (printType t1) ++ " no puede ser aplicado."

notKArgError :: Type -> Int -> Either String Type
notKArgError t1 k = err $ render (printType t1) ++ " no puede ser aplicado " ++ show k ++ " veces."

notfoundError :: Name -> Either String Type
notfoundError n = err $ show n ++ " no está definida."

-- infiere el tipo de un término a partir de un entorno local de variables y un entorno global
infer' :: Context -> NameEnv Value Type -> Term -> Either String Type
infer' c _ (Bound i)        = ret (c !! i)
infer' _ e (Free  n)        = case Prelude.lookup n e of 
                                Nothing     -> notfoundError n
                                Just (_, t) -> ret t
 
infer' c e (t :@: u)        = infer' c e t >>= \tt ->
                              infer' c e u >>= \tu ->
                              case tt of
                                FunT t1 t2 -> if (tu == t1)
                                              then ret t2
                                              else matchError t1 tu
                                _          -> notfunError tt

infer' c e (Lam t u)        = infer' (t : c) e u >>= \tu ->
                              ret $ FunT t tu

infer' c e (Let t1 t2)      = infer' c e t1 >>= \tt1 ->
                              infer' (tt1 : c) e t2  >>= \tt2 ->
                              ret tt2

infer' c e Zero             = ret NatT
infer' c e (Suc t)          = infer' c e t >>= \tt ->
                                case tt of 
                                  NatT -> ret NatT
                                  tt   -> matchError NatT tt

infer' c e (Rec t1 t2 t3)   = infer' c e t1 >>= \tt1 ->
                              infer' c e t2 >>= \tt2 ->
                              infer' c e t3 >>= \tt3 ->
                              if (tt3 /= NatT)  then matchError NatT tt3  
                                                else case tt2 of 
                                                  (FunT  x (FunT y z)) -> if (x == tt1 && y == NatT && z == tt1)
                                                                          then ret tt1
                                                                          else matchError t tt2     
                                                                          where t = (FunT tt1 (FunT NatT tt1))
                                                  _                    -> notKArgError tt2 2

infer' c e Nil              = ret ListT
infer' c e (Cons t1 t2)     = infer' c e t1 >>= \tt1 ->
                              infer' c e t2 >>= \tt2 ->
                              case tt1 of 
                                NatT -> if (tt2 == ListT)
                                        then ret tt2
                                        else matchError ListT tt2
                                _    -> matchError NatT tt1 

infer' c e (RecL t1 t2 t3)  = infer' c e t1 >>= \tt1 ->
                              infer' c e t2 >>= \tt2 ->
                              infer' c e t3 >>= \tt3 -> 
                              if    (tt3 /= ListT)
                              then  matchError ListT tt3
                              else  case tt2 of
                                      (FunT x (FunT y (FunT z r)))  ->  if match
                                                                        then ret tt1
                                                                        else matchError t tt2
                                                                        where match = (x == NatT)  &&
                                                                                      (y == ListT) &&
                                                                                      (z == tt1)   &&
                                                                                      (r == tt1)
                                                                              t     = FunT NatT
                                                                                           (FunT ListT (FunT tt1 tt1))

                                      _                             ->  notKArgError tt2 3

