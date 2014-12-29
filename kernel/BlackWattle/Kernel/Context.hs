{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}

{- Context.hs --- theorem contexts

-}

module BlackWattle.Kernel.Context where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (isJust)
import           Data.Monoid
import           Data.Set (Set)
import qualified Data.Set as S
import qualified Text.PrettyPrint as P
import           Text.PrettyPrint hiding (parens)

import           BlackWattle.Kernel.Types
import           BlackWattle.Kernel.Term
import           BlackWattle.Kernel.Theorem

-- * Contexts

-- To avoid clashing with Lens ...

data Ctxt = Ctxt { _freeTypes   :: Set TConstName            -- ^ Those types which are free
                 , _freeConstNames  :: Set ConstName             -- ^ Those consts which are free 
                 , _types       :: Map TConstName  Int       -- ^ All types and their 
                 , _consts      :: Map ConstName   Type      -- ^ All consts and their types
                 , _theorems    :: Map TheoremName Term  -- ^ Theorems in context
                 }
           deriving Show

makeLenses ''Ctxt

-- * Utility functions

maybeToError :: MonadError e m => e -> Maybe a -> m a
maybeToError e v = case v of
                     Nothing -> throwError e
                     Just v' -> return v'

-- | Internal only!
-- runContextM :: [Context] -> ContextM st a -> a
-- runContextM ctxt m = runReader (unContextM m) ctxt

addAxiom :: TheoremName -> Term -> Ctxt -> Ctxt
addAxiom = addTheorem -- Mainly for documentation

addTheorem :: TheoremName -> Term -> Ctxt -> Ctxt
addTheorem thmN tm = theorems . at thmN .~ Just tm

addConst :: ConstName -> Type -> Ctxt -> Ctxt
addConst nm ty   = consts . at nm .~ Just ty

addType :: TConstName -> Int -> Ctxt -> Ctxt
addType nm arity = types . at nm .~ Just arity

defineConst :: FQName ConstName -> TheoremName -> Type -> Term -> Ctxt -> Ctxt
defineConst nm thmN ty def ctxt = addTheorem thmN
                                             (mkEq ty (Constant nm ty) def)
                                             (addConst (fqnName nm) ty ctxt)
