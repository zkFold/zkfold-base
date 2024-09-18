{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.Commit (Commit (..), HomomorphicCommit (..), PedersonSetup (..)) where

import           Data.Foldable                               (Foldable, toList)
import           Prelude                                     (type (~), zipWith, ($), (<$>))
import qualified Prelude                                     as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.EllipticCurve.Class     as EC
import           ZkFold.Base.Algebra.EllipticCurve.Ed25519
import           ZkFold.Base.Protocol.Protostar.Oracle
import           ZkFold.Symbolic.Class

-- | Commit to the object @a@ with commitment key @ck@ and results of type @f@
--
class Commit ck a f where
    commit :: ck -> a -> f

instance (RandomOracle ck x, RandomOracle a x, Ring x) => Commit ck a x where
    commit ck a = oracle [oracle @ck @x ck, oracle @a @x a]

-- | Homomorphic commitment scheme, i.e. (hcommit ck1 a1) * (hcommit ck2 a2) == hcommit (ck1 + ck2) (a1 + a2)
--
class HomomorphicCommit ck a c where
    hcommit :: ck -> a -> c

class PedersonSetup a where
    pedersonGH :: (a, a)

instance PedersonSetup (Point BLS12_381_G1) where
    pedersonGH = (g, h)
        where
            -- Random points on BLS12_381_G1
            -- The only requirement for them is so that nobody knows discrete logarithm of g base h
            -- Keeping these numbers open seems safe as there is no known efficient algorithm to calculate discrete logarithm
            -- TODO: Consider choosing these elements randomly each time instead of hardcoding them
            g = Point
                  374634537115484260972239972618177817162837837681489433937595987156473628121582176081070052390732339994821123215324
                  3101937092382348684068486219386062896291823016251987968533318607938307290692317713596471528583601314350111497326114

            h = Point
                  89212312271530513649036778047014309438687633223023480439497929919626414549107721779839342336160039318198182187102
                  1428833674135004724206317422667541391548200977592780696082498356495280179807693517101023736214529698214586243870416

instance
  ( Symbolic c
  , FromConstant Natural (EC.BaseField (Ed25519 c))
  )=> PedersonSetup (Point (Ed25519 c)) where
    pedersonGH = (g, h)
        where
            -- Random points on Ed25519
            -- The only requirement for them is so that nobody knows discrete logarithm of g base h
            -- Keeping these numbers open seems safe as there is no known efficient algorithm to calculate discrete logarithm
            -- TODO: Consider choosing these elements randomly each time instead of hardcoding them
            g = Point
                  (fromConstant @Natural 45227885944482439959027551729127369191274275081056396600348249292591790930260)
                  (fromConstant @Natural 9659338654347744907807571808778983510552562195096080698048062169240435167699)

            h = Point
                  (fromConstant @Natural 11786464992768388791034908016886244722767117967376829028161961151214849049496)
                  (fromConstant @Natural 37077270161988888430676469598430826385740357039952739548288460740953233965539)

-- | Pedersen commitment scheme
-- Commitment key consists of field elements g and h, and randomness r
--
instance {-# OVERLAPPABLE #-}
    ( P.Eq a
    , P.Eq b
    , BinaryExpansion a
    , BinaryExpansion b
    , Bits a ~ [a]
    , Bits b ~ [b]
    , EllipticCurve c
    , PedersonSetup (Point c)
    ) => HomomorphicCommit a b (Point c) where
    hcommit r b = let (g, h) = pedersonGH @(Point c)
                   in pointMul b g + pointMul r h


-- Pedersen commitment scheme for lists extending the homomorphism to elementwise sums:
-- (hcommit ck l1) + (hcommit ck l2) = hcommit ck (zipWith (+) l1 l2), provided l1 and l2 have the same length.
-- This is required for AccumulatorScheme
--
instance (EllipticCurve c, HomomorphicCommit a b (Point c), Foldable t) => HomomorphicCommit a (t b) (Point c) where
    hcommit ck t = sum $ zipWith pointMul [1 :: Natural ..] (hcommit ck <$> toList t)


