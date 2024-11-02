{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TypeOperators             #-}

module ZkFold.UPLC.Normalization where

import           Data.Bool                       (otherwise)
import           Data.Eq                         ((==))
import           Data.Foldable                   (Foldable, null)
import           Data.Function                   (($))
import           Data.Functor                    (Functor, fmap)
import           Data.List                       (map, (++))
import           Data.Ord                        ((<), (>=))
import           Numeric.Natural                 (Natural)
import           Prelude                         (error, fromIntegral, succ)

import           ZkFold.Base.Algebra.Basic.Class ((+), (-!))
import           ZkFold.Prelude                  (length, splitAt, (!!))
import           ZkFold.UPLC.BuiltinFunction
import           ZkFold.UPLC.BuiltinType         (BuiltinType)
import           ZkFold.UPLC.Term

data Normalized = NLam Natural BodyNF

data BodyNF
  = NCall CallNF
  | forall t. NConstant !(Constant t)
  | NConstr !ConstructorTag [Normalized]
  | NError

data CallNF
  = NApp HeadNF [Normalized]
  | NCase CallNF [Normalized]
  | forall s t. NPoly !(BuiltinPolyFunction s t) (Untyped s Normalized)

data Untyped (s :: [BuiltinType]) a where
  UNil :: Untyped '[] a
  (:::) :: a -> Untyped s a -> Untyped (t ': s) a

infixr 0 :::

deriving instance Foldable (Untyped s)
deriving instance Functor (Untyped s)

data HeadNF
  = NVariable DeBruijnIndex
  | forall s t. NMono !(BuiltinMonoFunction s t)

normalize :: Term -> Normalized
normalize term = nf [] term []
  where
    nf :: [Normalized] -> Term -> [Normalized] -> Normalized
    nf ctx t args = case t of
      TVariable i
        | i < length ctx -> apply ctx (ctx !! i) args
        | otherwise -> error "Open term"
      TConstant c
        | null args -> NLam 0 (NConstant c)
        | otherwise -> error "Applying args to constant"
      TBuiltin (BFMono f) -> NLam 0 $ NCall $ NApp (NMono f) args
      TBuiltin (BFPoly f) ->
        let vars = fmap var (argsOf f)
         in apply ctx (NLam (length vars) $ NCall $ NPoly f vars) args
      TLam f -> case args of
        [] -> let ctx' = var 0 : map (shiftLam 1 0) ctx
                  NLam n body = nf ctx' f []
               in NLam (succ n) body
        arg:args' -> nf (arg : ctx) f args'
      TApp f u -> nf ctx f (nf ctx u [] : args)
      TDelay t' -> nf ctx t' args
      TForce t' -> nf ctx t' args
      TConstr tag ts
        | null args -> NLam 0 $ NConstr tag [nf ctx f [] | f <- ts]
        | otherwise -> error "Applying args to constructor"
      TCase t' bs ->
        let NLam n body = nf ctx t' []
         in if n == 0
            then case body of
              NCall c
                | null args -> NLam 0 $ NCall $ NCase c [nf ctx b [] | b <- bs]
                | otherwise -> error "Unknown match size"
              NConstant _    -> error "Applying case to constant"
              NConstr tag fs -> nf ctx (bs !! fromIntegral tag) (fs ++ args)
              NError         -> NLam 0 NError
            else error "Applying case to function"
      TError -> NLam 0 NError

    var :: DeBruijnIndex -> Normalized
    var i = NLam 0 $ NCall $ NApp (NVariable i) []

    argsOf :: BuiltinPolyFunction s t -> Untyped s DeBruijnIndex
    argsOf IfThenElse = three
    argsOf ChooseUnit = two
    argsOf Trace = two
    argsOf FstPair = one
    argsOf SndPair = one
    argsOf (BPFList f) = case f of
      ChooseList -> three
      MkCons     -> two
      HeadList   -> one
      TailList   -> one
      NullList   -> one
    argsOf ChooseData = 5 ::: 4 ::: 3 ::: three

    one = (0 :: DeBruijnIndex) ::: UNil
    two = 1 ::: one
    three = 2 ::: two

    shiftLam :: Natural -> Natural -> Normalized -> Normalized
    shiftLam d m (NLam n body) = NLam n (shiftBody d (n + m) body)

    shiftBody :: Natural -> Natural -> BodyNF -> BodyNF
    shiftBody d n (NCall c)      = NCall (shiftCall d n c)
    shiftBody _ _ (NConstant c)  = NConstant c
    shiftBody d n (NConstr t fs) = NConstr t (map (shiftLam d n) fs)
    shiftBody _ _ NError         = NError

    shiftCall :: Natural -> Natural -> CallNF -> CallNF
    shiftCall d n (NApp f ts)  = NApp (shiftHead d n f) (map (shiftLam d n) ts)
    shiftCall d n (NCase s bs) = NCase (shiftCall d n s) (map (shiftLam d n) bs)
    shiftCall d n (NPoly f ts) = NPoly f (fmap (shiftLam d n) ts)

    shiftHead :: Natural -> Natural -> HeadNF -> HeadNF
    shiftHead d n (NVariable i)
      | i >= n = NVariable (i + d)
      | otherwise = NVariable i
    shiftHead _ _ (NMono f) = NMono f

    apply :: [Normalized] -> Normalized -> [Normalized] -> Normalized
    apply ctx0 (NLam n body) args0
      | length args0 >= n =
        let (ctx1, args) = splitAt n args0
         in applyBody (ctx1 ++ ctx0) body args
      | otherwise =
        let d = n -! length args0
            ctx = [var i | i <- [0..d-!1]] ++ map (shiftLam d 0) (args0 ++ ctx0)
            NLam n' body' = applyBody ctx body []
         in NLam (d + n') body'

    applyBody :: [Normalized] -> BodyNF -> [Normalized] -> Normalized
    applyBody ctx body args = case body of
      NCall c -> applyCall ctx c args
      NConstant c
        | null args -> NLam 0 (NConstant c)
        | otherwise -> error "Applying args to constant"
      NConstr t fs
        | null args -> NLam 0 (NConstr t fs)
        | otherwise -> error "Applying args to constructor"
      NError -> NLam 0 NError

    applyCall :: [Normalized] -> CallNF -> [Normalized] -> Normalized
    applyCall ctx c args = case c of
      NApp f ts -> case f of
        NVariable i -> case ctx !! i of
          NLam 0 (NCall (NApp (NVariable j) [])) | i == j -> NLam 0 $ NCall $ NApp (NVariable i) (ts ++ args)
          other                                           -> apply ctx other (ts ++ args)
        other -> NLam 0 $ NCall $ NApp other (ts ++ args)
      NCase s bs ->
        let NLam n body = applyCall ctx s []
         in if n == 0
            then case body of
              NCall c'
                | null args -> NLam 0 $ NCall $ NCase c' [apply ctx b [] | b <- bs]
                | otherwise -> error "Unknown match size"
              NConstant _ -> error "Applying case to constant"
              NConstr tag fs -> apply ctx (bs !! fromIntegral tag) (fs ++ args)
              NError -> NLam 0 NError
            else error "Applying case to function"
      NPoly f ts -> NLam 0 $ NCall $ NPoly f $ propagate f ts (\x -> apply ctx x args)

    propagate :: BuiltinPolyFunction s t -> Untyped s Normalized -> (Normalized -> Normalized) -> Untyped s Normalized
    propagate IfThenElse (c ::: tail) f           = c ::: fmap f tail
    propagate ChooseUnit (u ::: tail) f           = u ::: fmap f tail
    propagate Trace (s ::: tail) f                = s ::: fmap f tail
    propagate (BPFList ChooseList) (l ::: tail) f = l ::: fmap f tail
    propagate ChooseData (d ::: tail) f           = d ::: fmap f tail
    propagate _ _ _                               = error "Applying args to builtin type"
