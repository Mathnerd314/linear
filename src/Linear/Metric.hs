{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2012-2013 Edward Kmett,
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Free metric spaces
----------------------------------------------------------------------------
module Linear.Metric
  ( Metric(..), normalize
  ) where

import Data.Foldable as Foldable
import Data.Functor.Identity
import Data.Vector (Vector)
import Data.IntMap (IntMap)
import Data.Map (Map)
import Data.HashMap.Strict (HashMap)
import Data.Hashable (Hashable)
import Linear.Epsilon
import Linear.Vector

-- $setup
-- >>> import Linear

-- | Free and sparse inner product/metric spaces.
class Additive v => Metric v where
  -- | Compute the inner product of two vectors or (equivalently)
  -- convert a vector @f a@ into a covector @f a -> a@.
  --
  -- >>> V2 1 2 `dot` V2 3 4
  -- 11
  dot :: v -> v -> Scalar v
#ifndef HLINT
  default dot :: (v ~ f a, Foldable f, ExtraStuff f, Scalar v ~ a, Num a) => f a -> f a -> a
  dot x y = Foldable.sum $ liftI2 (*) x y
#endif

  -- | Compute the squared norm. The name quadrance arises from
  -- Norman J. Wildberger's rational trigonometry.
  quadrance :: v -> Scalar v
  quadrance v = dot v v

  -- | Compute the quadrance of the difference
  qd :: v -> v -> Scalar v
  qd f g = quadrance (f ^-^ g)

  -- | Compute the norm of a vector in a metric space
  norm :: Floating (Scalar v) => v -> Scalar v
  norm v = sqrt (quadrance v)

  -- | Compute the distance between two vectors in a metric space
  distance :: Floating (Scalar v) => v -> v -> Scalar v
  distance f g = norm (f ^-^ g)

  -- | Convert a non-zero vector to unit vector.
  signorm :: Floating (Scalar v) => v -> v
  signorm v = v ^/ norm v

instance (Additive a, Fractional a) => Metric (Identity a) where
  dot (Identity x) (Identity y) = x * y

instance (Additive a, Fractional a) => Metric (IntMap a)

instance (Ord k, Additive a, Fractional a) => Metric (Map k a)

instance (Hashable k, Eq k, Additive a, Fractional a) => Metric (HashMap k a)

instance (Additive a, Fractional a) => Metric (Vector a)

-- | Normalize a 'Metric' functor to have unit 'norm'. This function
-- does not change the functor if its 'norm' is 0 or 1.
normalize :: (Floating (Scalar v), Metric v, Epsilon (Scalar v)) => v -> v
normalize v = if nearZero l || nearZero (1-l) then v else v ^/ sqrt l
  where l = quadrance v
