{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.IVC.AlgebraicMap (AlgebraicMap, algebraicMap) where

import           Data.ByteString                                     (ByteString)
import           Data.Functor.Rep                                    (Representable (..))
import           Data.Map.Strict                                     (Map, keys, insert)
import qualified Data.Map.Strict                                     as M
import           Prelude                                             (Either (..), Ord, fmap, zip, map,  error, ($))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Multivariate        as PM
import qualified ZkFold.Base.Data.Vector                             as V
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Base.Protocol.IVC.Predicate                  (Predicate (..))
import           ZkFold.Symbolic.Class                               (Symbolic(..))
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

-- | Algebraic map of @a@.
-- It calculates a system of equations defining @a@ in some way.
-- The inputs are polymorphic in a ring element @f@.
-- The main application is to define the verifier's algebraic map in the NARK protocol.
--
type AlgebraicMap k i f = i f -> Vector k [f] -> Vector (k-1) f -> f -> [f]

algebraicMap :: forall d k i p f ctx .
    ( KnownNat (d+1)
    , Representable i
    , Ord (Rep i)
    , Ring f
    , Scale (BaseField ctx) f
    )
    => Predicate i p ctx
    -> AlgebraicMap k i f
algebraicMap Predicate {..} = algMap
    where
        sys :: [PM.Poly (BaseField ctx) (SysVar i) Natural]
        sys = M.elems (acSystem predicateCircuit)

        sys' :: [PM.Poly (BaseField ctx) (Either () (SysVar i)) Natural]
        sys' = map (PM.mapVars Right) sys

        sys'' :: [PM.Poly (BaseField ctx) (Either () (SysVar i)) Natural]
        sys'' = map (padDecomposition @_ @d (Left ())) sys'

        algMap :: i f -> Vector k [f] -> Vector (k-1) f -> f -> [f]
        algMap pi pm _ pad =
            let
                witness :: Map ByteString f
                witness = M.fromList $ zip (keys $ acWitness predicateCircuit) (V.head pm)

                varMap :: Either () (SysVar i) -> f
                varMap (Left ())                      = pad
                varMap (Right (InVar inV))            = index pi inV
                varMap (Right (NewVar (EqVar newV)))  = M.findWithDefault zero newV witness
                varMap (Right (NewVar (FoldVar _ _))) = error "unexpected FOLD constraint"

                f_sps :: [f]
                f_sps = fmap (PM.evalPolynomial PM.evalMonomial varMap) sys''

            in f_sps

padDecomposition :: forall a d var .
    ( KnownNat (d+1)
    , Ord var
    ) => var -> PM.Poly a var Natural -> PM.Poly a var Natural
padDecomposition pad (PM.P ms) = PM.P $ map (\(c, PM.M m) -> (c, PM.M $ insert pad (d -! deg (PM.M m)) m)) ms
    where
        d = value @(d+1) -! 1

deg :: PM.Mono v Natural -> Natural
deg (PM.M m) = sum m
