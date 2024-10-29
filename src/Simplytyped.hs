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
conversion lt = conversionAux lt (M.empty)


type BoundedVars = M.Map String Int


conversionAux :: LamTerm -> BoundedVars -> Term
conversionAux (LVar x)      idxs  = case M.lookup x idxs of 
                                      Nothing -> Free (Global x)
                                      Just i  -> Bound i

conversionAux (LApp lt1 lt2) idxs = (conversionAux lt1 idxs) :@: 
                                    (conversionAux lt2 idxs)  

conversionAux (LAbs x t lt) idxs  = let
                                       idxs'  = M.map succ idxs
                                       idxs'' = M.insert x 0 idxs'
                                    in Lam t (conversionAux lt idxs'') 



conversionAux (LLet x lt1 lt2) idxs = let 
                                          idxs'  = M.map succ idxs
                                          idxs'' = M.insert x 0 idxs' 
                                      in  Let (conversionAux lt1 idxs) (conversionAux lt2 idxs'')  
                                          

-- (\x -> let y = 3 in x) 4
-- conversionAux (LLet x lt1 lt2) idxs = case M.lookup x idxs of 
--                                         Nothing -> Let (conversionAux lt1 idxs'') lt2'  -- Si esta libre, desplazo todos en 1 y pongo a la variable con indice 0
--                                         _       -> conversionAux lt2 idxs               -- Si esta ligada, no hago nada
--                                       where
--                                        idxs'  = M.map succ idxs
--                                        idxs'' = M.insert x 0 idxs'
--                                        lt2'    = conversionAux lt2 idxs''
                                        

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
-- sub i t (Let t'  u)           = Let t'



quote :: Value -> Term
quote (VLam t f) = Lam t f


-- evalúa un término en un entorno dado
eval :: NameEnv Value Type -> Term -> Value

eval _ (Bound j) = error "error: evaluating bounded variable"
eval ne (Free x) = case Prelude.lookup x ne of
                      Nothing     -> error "variable not in name enviroment"
                      Just (v, t) -> v 

eval ne (t1 :@: t2) = let
                        (Lam t f) = quote (eval ne t1)
                        t2'       = quote (eval ne t2')
                        tsub      = sub 0 t2' f 
                      
                      in eval ne tsub

eval ne (Let t1 t2) = let
                        t1'  = quote (eval ne t1)
                        tsub = sub 0 t1' t2
                      in
                        eval ne tsub

eval _ (Lam t f) = VLam t f



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

notfoundError :: Name -> Either String Type
notfoundError n = err $ show n ++ " no está definida."

-- infiere el tipo de un término a partir de un entorno local de variables y un entorno global
infer' :: Context -> NameEnv Value Type -> Term -> Either String Type
infer' c _ (Bound i) = ret (c !! i)
infer' _ e (Free  n) = case Prelude.lookup n e of 
  Nothing     -> notfoundError n
  Just (_, t) -> ret t
infer' c e (t :@: u) = infer' c e t >>= \tt -> infer' c e u >>= \tu ->
  case tt of
    FunT t1 t2 -> if (tu == t1) then ret t2 else matchError t1 tu
    _          -> notfunError tt

infer' c e (Lam t u)   = infer' (t : c) e u >>= \tu -> ret $ FunT t tu
infer' c e (Let t u) = infer' c e t >>= \tt -> infer' (tt : c) e u >>= \tu -> ret tu
