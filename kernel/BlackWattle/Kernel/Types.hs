{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PatternSynonyms #-}

module BlackWattle.Kernel.Types where

import           Control.Applicative (Applicative)
import           Control.Monad.Except
import           Control.Monad.State
import           Data.Data
import           Data.Functor
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

type Name  = String
type TVar  = String
type Const = String
type TConst = String

-- * Types

data Type = TFree TVar
          | TConst TConst [Type]
            deriving (Eq, Ord, Show, Data, Typeable)

-- * Term

infixl :$

data Term = Free { name :: Name, typ :: Type }
          | Bound { depth :: Int }
          | Const { name :: Const, typ :: Type }
          -- | The name here need not be unique, and should be converted before sending to user
          | Lambda { name :: Name, typ :: Type, body :: Term }
          -- | Applicatio, or Comb if you are that way inclined
          | (:$)   Term Term 
            deriving (Show, Data, Typeable)

-- | Equality on Terms is alpha equivalence
instance Eq Term where
    (Free v t) == (Free v' t')            = v == v' && t == t'
    (Bound n) == (Bound m)                = n == m
    (Const c t) == (Const c' t')          = c == c' && t == t'
    (Lambda _ tp t) == (Lambda _ tp' t')  = tp == tp' && t == t' -- Ignore names
    (tf :$ ta) == (tf' :$ ta')            = tf == tf' && ta == ta'
    _ == _                                = False

-- Hopefully this is more efficient than just <=
-- | Ordering on Terms ignored name annotations on binders
instance Ord Term where
    (Free n tp) `compare` (Free n' tp') = (n, tp) `compare` (n', tp')
    (Free {})   `compare` _             = LT

    (Bound {})  `compare` (Free {})     = GT
    (Bound n)   `compare` (Bound n')    = n `compare` n'
    (Bound {})  `compare` _             = LT

    (Const {})  `compare` (Free {})     = GT
    (Const {})  `compare` (Bound {})    = GT
    (Const c t) `compare` (Const c' t') = (c, t) `compare` (c', t')
    (Const {})  `compare` _             = LT

    (Lambda {}) `compare` (Free {})     = GT
    (Lambda {}) `compare` (Bound {})    = GT
    (Lambda {}) `compare` (Const {})    = GT
    (Lambda _ tp t) `compare` (Lambda _ tp' t')  = (tp, t) `compare` (tp', t')
    (Lambda {}) `compare` _             = LT

    (l :$ r) `compare` (l' :$ r')       = (l, r) `compare` (l', r')
    (_ :$ _) `compare` _                = GT

-- * Theorems
    
type TheoremName = String
type CTypeSubst st = [(CType st, CType st)]
type CTermSubst st = [(CTerm st, CTerm st)]
type HypSet      = [Term]

-- There are 3 flavours of theorems:
--   1. Internal theorems
--   2. External theorems
--   3. Stored theorems
--
-- An internal theorems is the subject of the various proof rules
-- (functions); an external theorem is one which explicitly carries
-- its context; and a stored theorem is one which is internal to the
-- context tree.
--
-- They are related by
--
--           /--- lookupTheorem -->\                /--- extern ---->\ 
-- Stored --|                       |-- Internal --|                  |-- External
--           \<-- storeTheorem  ---/                \<-- intern -----/    
--
--
-- We might be able to unify these, but there are 3 logical views

-- TODO:
-- - Term namespaces. like foo.def
-- definitions
-- types

-- The 'st' ensures theorems can't escape this context (well, ensures
-- theorems aren't introduced.

data Theorem st = Theorem { thydeps    :: Set TheoremName
                          , hypotheses :: HypSet
                          , prop       :: Term } 
           deriving Show
                    
-- * Certified terms/types 

data CTerm st = CTerm Term Type
           deriving Show
                    
newtype CType st = CType { unCType :: Type }
    deriving Show

-- * Contexts

type ContextName = String

-- | The id '[]' is the root context
type ContextId   = [ContextName]

data Context = Context { freeTypes   :: Set TConst            -- ^ Those types which are free
                       , freeConsts  :: Set Const             -- ^ Those consts which are free 
                       , types       :: Map TConst  Int       -- ^ All types and their 
                       , consts      :: Map Const   Type      -- ^ All consts and their types
                       , theorems    :: Map TheoremName Term  -- ^ Theorems in context
                       }
           deriving Show
                    
data ContextTree = Node { ctContext  :: Context
                        , ctChildren :: Map ContextName ContextTree
                        }
           deriving Show
                    
newtype ContextM st a = ContextM { unContextM :: State [Context] a }
        deriving (Functor, Applicative, Monad)

newtype BWM a = BWM { unBWM :: ExceptT String (State ContextTree) a }

-- * Names

-- FIXME: move

pattern FunN   = "fun"
pattern BoolN  = "bool"
pattern EqualN = "equal"
pattern IndN   = "ind"
pattern TrueN  = "TRUE"
pattern AndN   = "AND"
pattern ImplN  = "IMPL"
pattern AllN   = "ALL"
pattern ExN    = "EX"
pattern OrN    = "OR"
pattern FalseN = "FALSE"
pattern NotN   = "NOT"
pattern Ex1N   = "EX1"

