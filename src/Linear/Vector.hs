{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE DefaultSignatures #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2012 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- Operations on free vector spaces.
-----------------------------------------------------------------------------
module Linear.Vector
  ( Additive(..), ExtraStuff(..)
  , E(..)
  -- , negated
  -- , (^*)
  -- , (*^)
  -- , (^/)
  , sumV
  , basis
  , basisFor
  , kronecker
  , outer
  , unit
  ) where

import Control.Applicative
import Control.Lens hiding(to)
import Data.Complex
import Data.Foldable as Foldable (Foldable, forM_, foldl')
import Data.HashMap.Lazy as HashMap
import Data.Hashable
import Data.IntMap as IntMap
import Data.Map as Map
import Data.Monoid (mempty)
import Data.Traversable (mapAccumL)
import Data.Vector as Vector
import Data.Vector.Mutable as Mutable
import GHC.Generics
import Linear.Instances ()

-- $setup
-- >>> import Linear.V2

-- | Basis element
newtype E t = E { el :: Lens' t (Scalar t) }

infixl 6 ^+^, ^-^
infixl 7 ^*, *^, ^/

class GAdditive f where
  gzero :: f a

class GExtraStuff f where
  gliftU2 :: (a -> a -> a) -> f a -> f a -> f a
  gliftI2 :: (a -> b -> c) -> f a -> f b -> f c

-- no instances for V1

instance GAdditive U1 where
  gzero = U1
  {-# INLINE gzero #-}

instance GExtraStuff U1 where
  gliftU2 _ U1 U1 = U1
  {-# INLINE gliftU2 #-}
  gliftI2 _ U1 U1 = U1
  {-# INLINE gliftI2 #-}

instance (GAdditive f, GAdditive g) => GAdditive (f :*: g) where
  gzero = gzero :*: gzero
  {-# INLINE gzero #-}


-- no instances for :+:

instance (GExtraStuff f, GExtraStuff g) => GExtraStuff (f :*: g) where
  gliftU2 f (a :*: b) (c :*: d) = gliftU2 f a c :*: gliftU2 f b d
  {-# INLINE gliftU2 #-}
  gliftI2 f (a :*: b) (c :*: d) = gliftI2 f a c :*: gliftI2 f b d
  {-# INLINE gliftI2 #-}

instance ExtraStuff f => GExtraStuff (Rec1 f) where
  gliftU2 f (Rec1 g) (Rec1 h) = Rec1 (liftU2 f g h)
  {-# INLINE gliftU2 #-}
  gliftI2 f (Rec1 g) (Rec1 h) = Rec1 (liftI2 f g h)
  {-# INLINE gliftI2 #-}

instance GAdditive f => GAdditive (M1 i c f) where
  gzero = M1 gzero
  {-# INLINE gzero #-}

instance (Additive c) => GAdditive (K1 i c) where
  gzero = K1 zero

instance GExtraStuff f => GExtraStuff (M1 i c f) where
  gliftU2 f (M1 g) (M1 h) = M1 (gliftU2 f g h)
  {-# INLINE gliftU2 #-}
  gliftI2 f (M1 g) (M1 h) = M1 (gliftI2 f g h)
  {-# INLINE gliftI2 #-}

instance GExtraStuff Par1 where
  gliftU2 f (Par1 a) (Par1 b) = Par1 (f a b)
  {-# INLINE gliftU2 #-}
  gliftI2 f (Par1 a) (Par1 b) = Par1 (f a b)
  {-# INLINE gliftI2 #-}


-- | A vector is an additive group with additional structure.
class Additive v where
  -- | The zero vector
  zero :: v
  default zero :: (GAdditive (Rep v), Generic v) => v
  zero = to gzero

  -- | Compute the sum of two vectors
  --
  -- >>> V2 1 2 ^+^ V2 3 4
  -- V2 4 6
  (^+^) :: v -> v -> v
  default (^+^) :: (v ~ f a, ExtraStuff f, Additive a) => f a -> f a -> f a
  (^+^) = liftU2 (^+^)
  {-# INLINE (^+^) #-}

  -- | Compute the difference between two vectors
  --
  -- >>> V2 4 5 - V2 3 1
  -- V2 1 4
  (^-^) :: v -> v -> v
  x ^-^ y = x ^+^ negated y
  {-# INLINE (^-^) #-}

  -- | Compute the negation of a vector
  --
  -- >>> negated (V2 2 4)
  -- V2 (-2) (-4)
  negated :: v -> v
  default negated :: (v ~ f a, Functor f, Additive a) => f a -> f a
  negated = fmap negated
  {-# INLINE negated #-}

  -- | A vector is an additive group with additional structure.
  --class VectorSpace v where

  type Scalar v :: *
  -- | Compute the left scalar product
  --
  -- >>> 2 *^ V2 3 4
  -- V2 6 8
  (*^) :: Scalar v -> v -> v
  default (*^) :: (v ~ f a, Functor f, Num a) => a -> f a -> f a
  (*^) a = fmap (a*)
  {-# INLINE (*^) #-}

  -- | Compute the right scalar product
  --
  -- >>> V2 3 4 ^* 2
  -- V2 6 8
  (^*) :: v -> Scalar v -> v
  default (^*) :: (v ~ f a, Functor f, Num a) => f a -> a -> f a
  f ^* a = fmap (*a) f
  {-# INLINE (^*) #-}

  -- | Compute division by a scalar on the right.
  (^/) :: v -> Scalar v -> v
  default (^/) :: (v ~ f a, Functor f, Fractional a) => f a -> a -> f a
  f ^/ a = fmap (/a) f
  {-# INLINE (^/) #-}

-- | Sum over multiple vectors
--
-- >>> sumV [V2 1 1, V2 3 4]
-- V2 4 5
sumV :: (Foldable f, Additive v) => f v -> v
sumV = Foldable.foldl' (^+^) zero
{-# INLINE sumV #-}

{-
-- | Linearly interpolate between two vectors.
lerp :: Num a => a -> f a -> f a -> f a
lerp alpha u v = alpha *^ u ^+^ (1 - alpha) *^ v
{-# INLINE lerp #-}
-}

-- | I moved these out because they're not part of Additive or GAdditive. The distinction between intersectionWith/unionWith seems artificial, IMO there should just be Applicative and you can use e.g. http://hackage.haskell.org/package/total-map for sparse vector spaces. But I've left it in pending discussion.
class ExtraStuff f where
  -- | Apply a function to merge the 'non-zero' components of two vectors, unioning the rest of the values.
  --
  -- * For a dense vector this is equivalent to 'liftA2'.
  --
  -- * For a sparse vector this is equivalent to 'unionWith'.
  liftU2 :: (a -> a -> a) -> f a -> f a -> f a
  default liftU2 :: Applicative f => (a -> a -> a) -> f a -> f a -> f a
  liftU2 = liftA2
  {-# INLINE liftU2 #-}

  -- | Apply a function to the components of two vectors.
  --
  -- * For a dense vector this is equivalent to 'liftA2'.
  --
  -- * For a sparse vector this is equivalent to 'intersectionWith'.
  liftI2 :: (a -> b -> c) -> f a -> f b -> f c
  default liftI2 :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
  liftI2 = liftA2
  {-# INLINE liftI2 #-}

instance (Additive a, Num a, Fractional a) => Additive (ZipList a) where
  type Scalar (ZipList a) = a

instance ExtraStuff ZipList

instance (Additive a, Num a, Fractional a) => Additive (Vector a) where
  type Scalar (Vector a) = a
  zero = mempty
  {-# INLINE zero #-}

instance ExtraStuff Vector where
  liftU2 f u v = case compare lu lv of
    LT | lu == 0   -> v
       | otherwise -> modify (\ w -> Foldable.forM_ [0..lu-1] $ \i -> unsafeWrite w i $ f (unsafeIndex u i) (unsafeIndex v i)) v
    EQ -> Vector.zipWith f u v
    GT | lv == 0   -> u
       | otherwise -> modify (\ w -> Foldable.forM_ [0..lv-1] $ \i -> unsafeWrite w i $ f (unsafeIndex u i) (unsafeIndex v i)) u
    where
      lu = Vector.length u
      lv = Vector.length v
  {-# INLINE liftU2 #-}
  liftI2 = Vector.zipWith
  {-# INLINE liftI2 #-}

instance (Additive a, Num a, Fractional a) => Additive (Maybe a) where
  type Scalar (Maybe a) = a
  zero = Nothing
  {-# INLINE zero #-}

instance ExtraStuff Maybe where
  liftU2 f (Just a) (Just b) = Just (f a b)
  liftU2 _ Nothing ys = ys
  liftU2 _ xs Nothing = xs
  {-# INLINE liftU2 #-}

instance (Additive a, Num a, Fractional a) => Additive [a] where
  type Scalar [a] = a
  zero = []
  {-# INLINE zero #-}

instance ExtraStuff [] where
  liftU2 f = go where
    go (x:xs) (y:ys) = f x y : go xs ys
    go [] ys = ys
    go xs [] = xs
  {-# INLINE liftU2 #-}
  liftI2 = Prelude.zipWith
  {-# INLINE liftI2 #-}

instance (Additive a, Num a, Fractional a) => Additive (IntMap a) where
  type Scalar (IntMap a) = a
  zero = IntMap.empty
  {-# INLINE zero #-}

instance ExtraStuff IntMap where
  liftU2 = IntMap.unionWith
  {-# INLINE liftU2 #-}
  liftI2 = IntMap.intersectionWith
  {-# INLINE liftI2 #-}

instance (Additive a, Num a, Fractional a, Ord k) => Additive (Map k a) where
  type Scalar (Map k a) = a
  zero = Map.empty
  {-# INLINE zero #-}

instance (Ord k) => ExtraStuff (Map k) where
  liftU2 = Map.unionWith
  {-# INLINE liftU2 #-}
  liftI2 = Map.intersectionWith
  {-# INLINE liftI2 #-}

instance (Additive a, Num a, Fractional a, Eq k, Hashable k) => Additive (HashMap k a) where
  type Scalar (HashMap k a) = a
  zero = HashMap.empty
  {-# INLINE zero #-}

instance (Eq k, Hashable k) => ExtraStuff (HashMap k) where
  liftU2 = HashMap.unionWith
  {-# INLINE liftU2 #-}
  liftI2 = HashMap.intersectionWith
  {-# INLINE liftI2 #-}

instance (Additive a, Num a, Fractional a) => Additive ((->) b a) where
  type Scalar ((->) b a) = a
  zero   = const 0
  {-# INLINE zero #-}

instance ExtraStuff ((->) b)

instance (Additive a, Num a, Fractional a) => Additive (Complex a) where
  type Scalar (Complex a) = a
  zero = 0 :+ 0
  {-# INLINE zero #-}

instance ExtraStuff Complex where
  liftU2 f (a :+ b) (c :+ d) = f a c :+ f b d
  {-# INLINE liftU2 #-}
  liftI2 f (a :+ b) (c :+ d) = f a c :+ f b d
  {-# INLINE liftI2 #-}

instance (Additive a, Num a, Fractional a) => Additive (Identity a) where
  type Scalar (Identity a) = a
  zero = Identity 0
  {-# INLINE zero #-}

instance ExtraStuff Identity

-- `SetOne` builds all combinations of the filler with one value from the choices list.
data SetOne a = SetOne { _filler :: !a, choices :: [a] }
instance Functor SetOne where
  fmap f (SetOne a os) = SetOne (f a) (fmap f os)
instance Applicative SetOne where
  pure a = SetOne a []
  SetOne f fs <*> SetOne a as = SetOne (f a) (Prelude.foldr ((:) . ($ a)) (Prelude.map f as) fs)

-- | Produce a default basis for a vector space. If the dimensionality
-- of the vector space is not statically known, see 'basisFor'.
basis :: (Applicative t, Traversable t, Num a) => [t a]
basis = choices $ traverse (\a -> SetOne 0 [a]) (pure 1)

-- | Produce a default basis for a vector space from which the
-- argument is drawn.
basisFor :: (Traversable t, Num a) => t b -> [t a]
basisFor = choices . traverse (\_ -> SetOne 0 [1])

-- | Produce a diagonal matrix from a vector.
kronecker :: (Traversable t, Num a) => t a -> t (t a)
kronecker v = fillFromList (choices $ traverse (\a -> SetOne 0 [a]) v) v

-- | Create a unit vector.
--
-- >>> unit _x :: V2 Int
-- V2 1 0
unit :: (Applicative t, Num a) => ASetter' (t a) a -> t a
unit l = set' l 1 (pure 0)

fillFromList :: Traversable t => [a] -> t b -> t a
fillFromList l = snd . mapAccumL aux l
  where aux (a:as) _ = (as, a)
        aux [] _ = error "too few elements in takeFromList"

-- | Outer (tensor) product of two vectors
outer :: (Functor f, a ~ Scalar g, Additive g) => f a -> g -> f g
outer a b = fmap (\x-> x *^ b) a
