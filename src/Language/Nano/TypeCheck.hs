{-# LANGUAGE FlexibleInstances, OverloadedStrings, BangPatterns #-}

module Language.Nano.TypeCheck where

import Language.Nano.Types
import Language.Nano.Parser

import qualified Data.List as L
import           Text.Printf (printf)  
import           Control.Exception (throw)

--------------------------------------------------------------------------------
typeOfFile :: FilePath -> IO Type
typeOfFile f = parseFile f >>= typeOfExpr

typeOfString :: String -> IO Type
typeOfString s = typeOfExpr (parseString s)

typeOfExpr :: Expr -> IO Type
typeOfExpr e = do
  let (!st, t) = infer initInferState preludeTypes e
  if (length (stSub st)) < 0 then throw (Error ("count Negative: " ++ show (stCnt st)))
  else return t

--------------------------------------------------------------------------------
-- Problem 1: Warm-up
--------------------------------------------------------------------------------

-- | Things that have free type variables
class HasTVars a where
  freeTVars :: a -> [TVar]

-- | Type variables of a type
instance HasTVars Type where
  freeTVars TInt         = []
  freeTVars TBool        = []
  freeTVars (t1 :=> t2)  = L.nub (freeTVars t1 ++ freeTVars t2)
  freeTVars (TVar x)     = [x]
  freeTVars (TList t)    = freeTVars t

-- | Free type variables of a poly-type (remove forall-bound vars)
instance HasTVars Poly where
  freeTVars (Mono t)        = freeTVars t
  freeTVars (Forall var p)  = L.delete var $ freeTVars p

-- | Free type variables of a type environment
instance HasTVars TypeEnv where
  freeTVars gamma   = concat [freeTVars s | (x, s) <- gamma]  
  
-- | Lookup a variable in the type environment  
lookupVarType :: Id -> TypeEnv -> Poly
lookupVarType x ((y, s) : gamma)
  | x == y    = s
  | otherwise = lookupVarType x gamma
lookupVarType x [] = throw (Error ("unbound variable: " ++ x))

-- | Extend the type environment with a new biding
extendTypeEnv :: Id -> Poly -> TypeEnv -> TypeEnv
extendTypeEnv x s gamma = (x,s) : gamma  

-- | Lookup a type variable in a substitution;
--   if not present, return the variable unchanged
lookupTVar :: TVar -> Subst -> Type
lookupTVar a [] = TVar a
lookupTVar a ((x, t) : sub)
  | a == x    = t
  | otherwise = lookupTVar a sub

-- | Remove a type variable from a substitution
removeTVar :: TVar -> Subst -> Subst
removeTVar a sub = filter (\(x, _) -> x /= a) sub
     
-- | Things to which type substitutions can be apply
class Substitutable a where
  apply :: Subst -> a -> a
  
-- | Apply substitution to type
instance Substitutable Type where
  apply sub TInt          = TInt
  apply sub TBool         = TBool
  apply sub (t1 :=> t2)   = apply sub t1 :=> apply sub t2
  apply sub (TVar a)      = lookupTVar a sub
  apply sub (TList t)     = TList $ apply sub t

-- | Apply substitution to poly-type
instance Substitutable Poly where
  apply sub (Mono t) = Mono (apply sub t)
  apply sub forall@(Forall var p) = 
    let sub' = removeTVar var sub
    in Forall var (apply sub' p)

-- | Apply substitution to (all poly-types in) another substitution
instance Substitutable Subst where  
  apply sub to = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip to
      
-- | Apply substitution to a type environment
instance Substitutable TypeEnv where  
  apply sub gamma = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip gamma
      
-- | Extend substitution with a new type assignment
extendSubst :: Subst -> TVar -> Type -> Subst
extendSubst sub a t = (a, apply sub t) : removeTVar a sub
      
--------------------------------------------------------------------------------
-- Problem 2: Unification
--------------------------------------------------------------------------------
      
-- | State of the type inference algorithm      
data InferState = InferState { 
    stSub :: Subst -- ^ current substitution
  , stCnt :: Int   -- ^ number of fresh type variables generated so far
} deriving (Eq,Show)

-- | Initial state: empty substitution; 0 type variables
initInferState = InferState [] 0

-- | Fresh type variable number n
freshTV n = TVar $ "a" ++ show n      
    
-- | Extend the current substitution of a state with a new type assignment   
extendState :: InferState -> TVar -> Type -> InferState
extendState (InferState sub n) a t = InferState (extendSubst sub a t) n
        
-- | Unify a type variable with a type; 
--   if successful return an updated state, otherwise throw an error
unifyTVar :: InferState -> TVar -> Type -> InferState
unifyTVar st@(InferState sub n) a t =
  if t == TVar a
  then st
  else if a `elem` freeTVars (apply sub t)
       then throw (Error "type error")
       else extendState st a t
    
-- | Unify two types;
--   if successful return an updated state, otherwise throw an error
unify :: InferState -> Type -> Type -> InferState
unify st t1 t2 = 
  case (t1, t2) of
    (TInt, TInt) -> st
    (TBool, TBool) -> st
    (TList t1, TList t2) -> unify st t1 t2
    (t1 :=> t2, t3 :=> t4) -> 
      let st' = unify st t1 t3
      in unify st' t2 t4
    (TVar a, t) -> unifyTVar st a t
    (t, TVar a) -> unifyTVar st a t
    _ | t1 == t2 -> st
      | otherwise -> throw (Error "type error")

--------------------------------------------------------------------------------
-- Problem 3: Type Inference
--------------------------------------------------------------------------------    
  
infer :: InferState -> TypeEnv -> Expr -> (InferState, Type)
infer st _ (EInt _) = (st, TInt)

infer st _ (EBool _) = (st, TBool)

infer st gamma (EVar x) =
    case lookup x gamma of
        Just s -> 
            let (newCnt, t) = instantiate (stCnt st) s
            in (st { stCnt = newCnt }, t)
        Nothing -> throw (Error ("unbound variable: " ++ x))

infer st gamma (ELam x body) =
  let freshTypeVar = freshTV (stCnt st)
      updatedState = st { stCnt = stCnt st + 1 }
      newGamma = extendTypeEnv x (Mono freshTypeVar) gamma
      (st', tBody) = infer updatedState newGamma body
  in (st', freshTypeVar :=> tBody)

infer st gamma (EApp e1 e2) = 
  let 
    (st1, t1) = infer st gamma e1
    (st2, t2) = infer st1 gamma e2
    freshResultType = freshTV (stCnt st2)
    st3 = st2 { stCnt = stCnt st2 + 1 }
    st4 = unify st3 t1 (t2 :=> freshResultType)
    resultType = apply (stSub st4) freshResultType
  in (st4, resultType)

infer st gamma (ELet x e1 e2) = 
    let freshType = freshTV (stCnt st)
        assumedGamma = extendTypeEnv x (Mono freshType) gamma
        (st1, t1) = infer (st { stCnt = stCnt st + 1 }) assumedGamma e1
        sub1 = stSub st1
        t1' = apply sub1 t1
        genType = generalize (apply sub1 gamma) t1'
        newGamma = extendTypeEnv x genType gamma
        (st2, t2) = infer st1 newGamma e2
    in (st2, t2)
    
infer st gamma (EBin op e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp opVar e1) e2
    opVar = EVar (show op)
infer st gamma (EIf c e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp (EApp ifVar c) e1) e2
    ifVar = EVar "if"    
infer st gamma ENil = infer st gamma (EVar "[]")

-- | Generalize type variables inside a type
generalize :: TypeEnv -> Type -> Poly
generalize gamma t =
    let tvars = freeTVars t
        boundVars = concatMap (freeTVars . snd) gamma
        freeVars = filter (`notElem` boundVars) tvars
    in foldr Forall (Mono t) freeVars
    
-- | Instantiate a polymorphic type into a mono-type with fresh type variables
instantiate :: Int -> Poly -> (Int, Type)
instantiate n (Mono t) = (n, t)
instantiate n (Forall var p) =
    let freshVar = freshTV n
        (n', t) = instantiate (n + 1) p
        subst = [(var, freshVar)]
    in (n', apply subst t)
      
-- | Types of built-in operators and functions      
preludeTypes :: TypeEnv
preludeTypes =
  [ ("+",    Mono $ TInt :=> TInt :=> TInt)
  , ("-",    Mono $ TInt :=> TInt :=> TInt)
  , ("*",    Mono $ TInt :=> TInt :=> TInt)
  , ("/",    Mono $ TInt :=> TInt :=> TInt)
  , ("==",   Forall "a" (Mono $ TVar "a" :=> TVar "a" :=> TBool))
  , ("!=",   Forall "a" (Mono $ TVar "a" :=> TVar "a" :=> TBool))
  , ("<",    Mono $ TInt :=> TInt :=> TBool)
  , ("<=",   Mono $ TInt :=> TInt :=> TBool)
  , ("&&",   Mono $ TBool :=> TBool :=> TBool)
  , ("||",   Mono $ TBool :=> TBool :=> TBool)
  , ("if",   Forall "b" (Mono $ TBool :=> TVar "b" :=> TVar "b" :=> TVar "b"))
  , ("[]",   Forall "c" (Mono $ TList (TVar "c")))
  , (":",    Forall "d" (Mono $ TVar "d" :=> TList (TVar "d") :=> TList (TVar "d")))
  , ("head", Forall "e" (Mono $ TList (TVar "e") :=> TVar "e"))
  , ("tail", Forall "f" (Mono $ TList (TVar "f") :=> TList (TVar "f")))
  ]
