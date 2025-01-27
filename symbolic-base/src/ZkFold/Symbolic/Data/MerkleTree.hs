{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}


module ZkFold.Symbolic.Data.MerkleTree where

import           Data.Foldable                     (foldlM)
import           Data.Functor.Rep                  (Representable, pureRep)
import qualified Data.List                         as LL
import           Data.Proxy                        (Proxy (Proxy))
import           Data.Type.Equality                (type (~))
import           GHC.Generics                      hiding (Rep, UInt, from)
import           GHC.TypeNats
import           Prelude                           (Traversable, const, return, zip, ($), (.))
import qualified Prelude                           as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Control.HApplicative  (hpair)
import           ZkFold.Base.Data.Package
import qualified ZkFold.Base.Data.Vector           as V
import           ZkFold.Base.Data.Vector           hiding ((.:))
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool         (Bool (..))
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators  (Iso (from), KnownRegisters, NumberOfRegisters, RegisterSize (Auto),
                                                    expansion, horner, mzipWithMRep)
import           ZkFold.Symbolic.Data.Conditional  (Conditional, bool)
import           ZkFold.Symbolic.Data.FieldElement (FieldElement (FieldElement, fromFieldElement))
import           ZkFold.Symbolic.Data.Input        (SymbolicInput)
import qualified ZkFold.Symbolic.Data.List         as L
import           ZkFold.Symbolic.Data.List
import qualified ZkFold.Symbolic.Data.Maybe        as M
import           ZkFold.Symbolic.Data.Maybe        (fromMaybe, just, nothing)
import           ZkFold.Symbolic.Data.Morph
import           ZkFold.Symbolic.Data.UInt         (UInt (..), strictConv)
import           ZkFold.Symbolic.Fold              (SymbolicFold)
import           ZkFold.Symbolic.MonadCircuit


data MerkleTree (d :: Natural) h = MerkleTree {
    mHash   :: (Context h) (Layout h)
  , mLevels :: Vector d (List (Context h) h)
  }
  deriving (Generic)

hashAux :: forall i m a w f. (MonadCircuit i a w m, Representable f, Traversable f) => Par1 i -> f i -> f i -> m (f i)
hashAux (Par1 b) h g = do
  v1 <- merkleHasher h g
  v2 <- merkleHasher g h
  mzipWithMRep (\wx wy -> newAssigned ((one - ($ b)) * ($ wx) + ($ b) * ($ wy))) v1 v2
  where
    merkleHasher :: f i -> f i -> m (f i)
    merkleHasher = P.undefined

instance (SymbolicData h, KnownNat d) => SymbolicData (MerkleTree d h)
instance (SymbolicInput h, KnownNat d) => SymbolicInput (MerkleTree d h)

-- | Finds an element satisfying the constraint
find :: forall h d c.
  ( Conditional (Bool c) h
  , SymbolicInput h
  , Context h ~ c
  , SymbolicFold c
  ) => MorphFrom c h (Bool c) -> MerkleTree d h -> M.Maybe c h
find p MerkleTree{..} =
  let leaves = V.last mLevels
      arr = L.filter p leaves
  in bool (just $ L.head arr) nothing (L.null arr)

newtype MerkleTreePath (d :: Natural) c = MerkleTreePath { mPath :: Vector (d-1) (Bool c)}
  deriving (Generic)

instance (Symbolic c, KnownNat (d-1)) => SymbolicData (MerkleTreePath d c)
instance (Symbolic c, KnownNat (d-1)) => Conditional (Bool c) (MerkleTreePath d c)

-- | Finds a path to an element satisfying the constraint
findPath :: forall x c d n.
  ( SymbolicOutput x
  , Context x ~ c
  , KnownNat d
  , KnownNat (d-1)
  , KnownNat (NumberOfRegisters (BaseField c) n Auto)
  , NumberOfBits (BaseField c) ~ n
  , SymbolicFold c, KnownRegisters c d Auto
  ) => MorphFrom c x (Bool c) -> MerkleTree d x -> M.Maybe c (MerkleTreePath d c)
findPath p mt@(MerkleTree _ nodes) =  bool (nothing @_ @c) (just path) (p @ lookup @x @c mt path :: Bool c)
  where
    leaves = V.last nodes
    path = MerkleTreePath . indToPath @c . fromFieldElement . from $ findIndex p leaves

indToPath :: forall c d.
  ( Symbolic c
  , KnownNat d
  ) => c Par1 -> Vector (d - 1) (Bool c)
indToPath e = P.fmap Bool . unpack $ fromCircuitF e $ \(Par1 i) -> do
    ee <- expansion (knownNat @d) i
    return $ Comp1 (V.unsafeToVector @(d-1) $ P.map Par1 ee)


-- | Returns the element corresponding to a path
lookup :: forall x c d.
  ( SymbolicOutput x
  , Context x ~ c
  , KnownNat (d - 1)
  , KnownNat d
  , SymbolicFold c, KnownRegisters c d Auto
  ) => MerkleTree d x -> MerkleTreePath d c -> x
lookup (MerkleTree root nodes) (MerkleTreePath p) = xA
  where
    xP = leaf @c @x @d (V.last nodes) $ ind path

    inits = V.unsafeToVector @(d-2) $
              LL.unfoldr (\v -> let initV = LL.init v
                                 in if LL.null initV then P.Nothing else P.Just (ind @_ @c (V.unsafeToVector initV), initV)) $ V.fromVector path

    cinds :: Vector (d-1) (c Par1)
    cinds = unpacked $ fromCircuit2F (pack path) (pack inits) $ \ps' is' -> do
      let ps = P.fmap unPar1 (unComp1 ps')
          is = V.unsafeToVector @(d-1) (fromConstant @(BaseField c) zero : (V.fromVector . P.fmap unPar1 $ unComp1 is'))
      mzipWithMRep (\wp wi -> newAssigned (one - ($ wp) + ($ wi)*(one + one))) ps is

    pairs = V.unsafeToVector @(d-1) $ P.zipWith (\l i -> arithmetize (leaf @c @x @d l i) Proxy) (V.fromVector $ V.tail nodes) (V.fromVector cinds)

    xA = restore @x @c $ const (preimage , payload xP Proxy)

    rootAndH1 :: Context x (Layout x :*: Layout x)
    rootAndH1 = hpair root (arithmetize xP Proxy)

    preimage :: c (Layout x)
    preimage = fromCircuit3F (pack pairs) (pack path) rootAndH1 $ \ g p' r' -> do
      let gs = V.fromVector $ unComp1 g
          bs = V.fromVector $ unComp1 p'
          (r :*: h1) = r'
      hd :: Layout x i <- foldlM (\h' (g', b') -> hashAux b' h' g') h1 $ zip gs bs
      _ <- mzipWithMRep (\wx wy -> constraint (($ wx) - ($ wy))) hd r
      return h1

    path :: Vector (d - 1) (c Par1)
    path = P.fmap (\(Bool b) -> b) p


leaf :: forall c x d.
  (SymbolicOutput x, SymbolicFold c, KnownRegisters c d Auto, Context x ~ c, KnownNat d
  ) => List c x -> c Par1 -> x
leaf l i = let num = strictConv @_ @(UInt d Auto c) i in l L.!! num


ind :: forall d c. (Symbolic c) => Vector d (c Par1) -> c Par1
ind vb = fromCircuitF (pack vb) $ \vb' -> do
  let bs = P.map unPar1 $ V.fromVector $ unComp1 vb'
  b1n <- P.fmap Par1 . horner $ bs
  return $ fromConstant b1n

-- | Inserts an element at a specified position in a tree
insertLeaf :: forall x c d.
  ( SymbolicOutput x
  , Context x ~ c
  , KnownNat (d - 1)
  , KnownNat d
  , SymbolicFold c
  , KnownRegisters c d Auto
  ) => MerkleTree d x -> MerkleTreePath d c -> x -> MerkleTree d x
insertLeaf (MerkleTree _ nodes) (MerkleTreePath p) xI = MerkleTree (V.head preimage) (V.unsafeToVector z3)
  where
    inits = V.unsafeToVector @(d-2) $
              LL.unfoldr (\v -> let initV = LL.init v
                                 in if LL.null initV then P.Nothing else P.Just (ind @_ @c (V.unsafeToVector initV), initV)) $ V.fromVector path

    cinds :: Vector (d-1) (c Par1)
    cinds = unpacked $ fromCircuit2F (pack path) (pack inits) $ \ps' is' -> do
      let ps = P.fmap unPar1 (unComp1 ps')
          is = V.unsafeToVector @(d-1) (fromConstant @(BaseField c) zero : (V.fromVector . P.fmap unPar1 $ unComp1 is'))
      mzipWithMRep (\wp wi -> newAssigned (one - ($ wp) + ($ wi)*(one + one))) ps is

    pairs = V.unsafeToVector @(d-1) $ P.zipWith (\l i -> arithmetize (leaf @c @x @d l i) Proxy) (V.fromVector $ V.tail nodes) (V.fromVector cinds)

    preimage :: Vector (d - 1) (c (Layout x))
    preimage = unpack $ fromCircuit3F (pack pairs) (pack path) (arithmetize xI Proxy) $ \ g p' h1 -> do
      let gs = V.fromVector $ unComp1 g
          bs = V.fromVector $ unComp1 p'
      hd <- helper h1 (zip gs bs)
      return $ Comp1 $ V.unsafeToVector @(d-1) hd

    helper :: forall i m a w f. (MonadCircuit i a w m, Representable f, Traversable f) => f i -> [(f i, Par1 i)] -> m [f i]
    helper _ [] = return []
    helper h (pi:ps) = do
      let (g, b) = pi
      hN <- hashAux b h g
      (hN :) P.<$> helper hN ps

    path :: Vector (d - 1) (c Par1)
    path = P.fmap (\(Bool b) -> b) p

    z3 = P.zipWith3 (\l mtp xi -> L.insert l mtp (restore @_ @c $ const (xi, pureRep zero)))
          (V.fromVector nodes)
          (P.map (strictConv @_ @(UInt d Auto c)) ([embed $ Par1 zero] P.++ V.fromVector inits P.++ [ind path]))
          (V.fromVector preimage P.<> [arithmetize xI Proxy])

-- | Replaces an element satisfying the constraint. A composition of `findPath` and `insert`
replace :: forall x c d n.
  ( SymbolicOutput x
  , Context x ~ c
  , KnownNat d
  , KnownNat (d-1)
  , KnownNat (NumberOfRegisters (BaseField c) n Auto)
  , NumberOfBits (BaseField c) ~ n
  , SymbolicFold c, KnownRegisters c d Auto
  ) => MorphFrom c x (Bool c) -> MerkleTree d x -> x -> MerkleTree d x
replace p t = insertLeaf t (fromMaybe (P.error "That Leaf does not exist") $ findPath @x @c p t)

-- | Returns the next path in a tree
incrementPath :: forall c d.
  ( KnownNat d
  , Symbolic c
  ) => MerkleTreePath d c -> MerkleTreePath d c
incrementPath (MerkleTreePath p) =
  MerkleTreePath . indToPath @c $ fromFieldElement (FieldElement (ind $ P.fmap (\(Bool b) -> b) p) + one)
