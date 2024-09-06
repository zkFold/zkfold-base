{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.Commit (Commit (..), HomomorphicCommit (..), PedersonSetup (..)) where

import           Prelude                                     (type (~), zipWith, ($), (<$>))
import qualified Prelude                                     as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Protocol.Protostar.Oracle

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
    ) => HomomorphicCommit a b (Point BLS12_381_G1) where
    hcommit r b = let (g, h) = pedersonGH @(Point BLS12_381_G1)
                   in pointMul b g -- + pointMul r h


-- Pedersen commitment scheme for lists extending the homomorphism to elementwise sums:
-- (hcommit ck l1) + (hcommit ck l2) = hcommit ck (zipWith (+) l1 l2)
-- This is required for AccumulatorScheme
--
instance HomomorphicCommit a b (Point BLS12_381_G1) => HomomorphicCommit a [b] (Point BLS12_381_G1) where
    hcommit ck lst = sum $ zipWith pointMul [1 :: Natural ..] (hcommit ck <$> lst)
