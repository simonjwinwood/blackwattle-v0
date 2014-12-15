
module BlackWattle.Util.Update where

import Control.Applicative
import Control.Comonad

import Data.Maybe (maybe)

data Update a = Old a | New a

taint :: Update a -> Update a
taint = New . extract

project :: Update a -> a
project (Old a) = a
project (New a) = a

instance Functor Update where
    fmap f (Old a) = Old (f a)
    fmap f (New a) = New (f a)

instance Applicative Update where
    pure f              = Old f
    (Old f) <*> (Old v) = Old (f v)
    f <*> v             = New (extract f $ extract v) -- taints

instance Monad Update where
    return              = Old
    (Old v) >>= f       = f v
    (New v) >>= f       = taint $ f v

-- | For what it is worth ...
-- Proofs (at least for strict application):
-- @
--  (extract . duplicate) (C a) = extract (C (C a)) = C a = id (C a)
--  (fmap extract . duplicate) (C a) = fmap extract (C (C a)) = C a = id (C a)
--  (duplicate . duplicate) (C a) = duplicate (C (C a)) 
--                                = C (C (C a))
--                                = C (duplicate (C a)) 
--                                = fmap duplicate (C (C a))
--                                = (fmap duplicate . duplicate) (C a)    
-- @
instance Comonad Update where
    extract (Old a) = a
    extract (New a) = a
    -- extend :: (Update a -> b) -> Update a -> Update b
    -- extend f = fmap f . duplicate
    -- duplicate :: Update a -> Update (Update a) 
    duplicate (Old a) = Old (Old a)
    duplicate (New a) = New (New a)

instance ComonadApply Update where
    (<@>) = (<*>)

infixl <||> 
v <||> v' = case v of
              Old _ -> v'
              New y -> v

infixl 2 <!>
v <!> x = case v of
            Old _ -> Old x
            New y -> v

liftUpdate :: (a -> Maybe a) -> a -> Update a
liftUpdate f a = maybe (Old a) New (f a)
