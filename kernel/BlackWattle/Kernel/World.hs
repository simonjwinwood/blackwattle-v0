{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE GADTs #-}

module BlackWattle.Kernel.World where

import           Control.Applicative
import           Control.Lens
import           Control.Monad.Reader
import           Data.List (inits)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (isNothing, listToMaybe, catMaybes)
import           Data.Set (Set)
import qualified Data.Set as S

import           BlackWattle.Kernel.Types
import           BlackWattle.Kernel.Term
import           BlackWattle.Kernel.Theorem
import           BlackWattle.Kernel.Context

class Monad m => MonadWorld (m :: * -> *) where
  type WorldTag m
  currentWorld     :: m World
  currentContextId :: m ContextId

class Externable f where
  type ExternType f
  extern :: MonadWorld m => f (WorldTag m)   -> m (ExternType f)
  intern :: MonadWorld m => ExternType f     -> m (Maybe (f (WorldTag m))) -- Either Reason (f st) ??

-- BlackWattleMonad, or BWM for short
-- newtype BWM a = BWM { unBWM :: ExceptT String (State Universe) a }

-- FIXME: add extend | mutate flag
data WorldMorphism = TypeMorphism  ContextId ConstName ExtTheorem
--                   | ConstMorphism FullConstName  Term

data World    = World    { _contextTree :: ContextTree } -- ... and the dep. graphs

-- Mainly the current world, and a cache of previous worlds.
data Universe = Universe { worlds :: [(WorldMorphism, World)] } 

data WorldMState = WMS { _contextId :: ContextId
                        , _world     :: World
                        }

newtype WorldT st m a = WorldT { unWorldM :: ReaderT WorldMState m a }
        deriving (Functor, Applicative, Monad, MonadReader WorldMState, MonadTrans)

type WorldM st a = WorldT st Identity a

data ContextTree = ContextTree { _ctContext  :: Ctxt
                               , _ctChildren :: Map ContextName ContextTree
                               }
           deriving Show

makeLenses ''World
makeLenses ''WorldMState
makeLenses ''ContextTree

instance Monad m => MonadWorld (WorldT st m) where
  type WorldTag (WorldT st m) = st
  currentWorld     = view world
  currentContextId = view contextId

runWorldT :: ContextId -> World -> (forall st. WorldT st m a) -> m a
runWorldT cid w m = runReaderT (unWorldM m) (WMS cid w)

runWorldM :: ContextId -> World -> (forall st. WorldM st a) -> a
runWorldM cid w m = runReader (unWorldM m) (WMS cid w)

-- FIXME!!
instance Externable Theorem where
  type ExternType Theorem = ExtTheorem
  extern thm = return $ ExtTheorem { extThmDeps = M.empty
                                   , extTypes   = M.empty
                                   , extConsts  = M.empty
                                   , extHyps    = hypotheses thm
                                   , extProp    = prop thm
                                   }
  intern ethm = return .Just $ Theorem { thmDeps    = S.empty
                                       , hypotheses = extHyps ethm
                                       , prop       = extProp ethm
                                       }

contextIdToTraversal :: ContextId -> Traversal' ContextTree Ctxt
contextIdToTraversal = go
  where
    go []        = ctContext
    go (c : cid) = ctChildren . ix c . go cid

resolve :: Lens' Ctxt (Maybe a) -> WorldM st (Maybe (ContextId, a))
resolve l = go <$> view (world . contextTree) <*> view contextId
  where
    tryOne tree cid  = (cid, ) <$> join (tree ^? contextIdToTraversal cid . l)
    go tree = listToMaybe . catMaybes . map (tryOne tree) . reverse . inits

resolveType :: TConstName -> WorldM st (Maybe (ContextId, Int))
resolveType tconstN = resolve (types . at tconstN)

resolveConst :: ConstName -> WorldM st (Maybe (ContextId, Type))
resolveConst constN = resolve (consts . at constN)

resolveTheorem :: TheoremName -> WorldM st (Maybe (Theorem st))
resolveTheorem thmN = do m_tm <- resolve (theorems . at thmN)
                         case m_tm of
                           Nothing        -> return Nothing
                           Just (_cid, tm) -> return .Just$ (emptyTheorem tm) { thmDeps = S.singleton thmN }

-- returns the deepest context first (reverse search order)
-- contextTreePath :: ContextId -> ContextTree -> Maybe [Context]
-- contextTreePath = go []
--   where
--    go acc cid tree = let acc' = ctContext tree : acc
--                      in case cid of
--                           []         -> return acc'
--                           (c : cid') -> go acc' cid' =<< M.lookup c (ctChildren tree)

rootContextId :: ContextId
rootContextId  = []

applyMorphism :: WorldMorphism -> World -> Maybe World
applyMorphism (TypeMorphism cid n ethm) = newType cid n ethm (n ++ "_abs") (n ++ "_rep") (n ++ "_thm1") (n ++ "_thm2")

-- | This adds a new type, defined as a subset of an existing type:
-- the theorem 'thm' should be
--
--  [] |- P t
--
-- where P is the predicate defining the subset.
--
-- Output are 2 theorems,
--
--  [] |- !a : . abs (rep a) = a
--  [] |- !r. P r = (rep (abs r) = r)

newType :: ContextId       -- ^ Where to add new type
           -> TConstName   -- ^ Name of new type
           -> ExtTheorem   -- ^ Witnessing theorem
           -> ConstName    -- ^ Rep name
           -> ConstName    -- ^ Abs name
           -> TheoremName  -- ^ Theorem 1
           -> TheoremName  -- ^ Theorem 2
           -> World -> Maybe World
newType cid typeN ethm absN repN thmN1 thmN2 w
  = do p :$ t <- runWorldM cid w (fmap (fmap prop) $ intern ethm)
       -- guard (null $ hypotheses thm)
       -- p :$ t <- return $ prop thm
       ctraverse (doIt p t) w
   where
     ctraverse  = contextTree . contextIdToTraversal cid
     doIt p t c = do let checkUnbound :: Ord a => a -> Lens' Ctxt (Map a b) -> Maybe ()
                         checkUnbound n l = guard (c ^. l . to (not . M.member n))
                     checkUnbound typeN types
                     checkUnbound absN  consts
                     checkUnbound repN  consts
                     checkUnbound thmN1 theorems
                     checkUnbound thmN2 theorems
                     -- Go time ...
                     let tfrees  = freeTypesInTerm p
                         arity   = length tfrees
                         rty     = typeOf t
                         aty     = TConst typeN (map TFree tfrees)
                         abs_tm  = Constant absN (rty :-> aty)
                         rep_tm  = Constant repN (aty :-> rty)
                         a_var   = Free "a" aty
                         r_var   = Free "r" rty
                         a_r_thm = mkEq aty (abs_tm :$ (rep_tm :$ a_var)) a_var 
                         r_a_thm = mkEq rty (p :$ r_var) (rep_tm :$ (abs_tm :$ r_var))
                     return . addTheorem thmN1 a_r_thm
                            . addTheorem thmN2 r_a_thm
                            . addType typeN arity
                            . addConst absN (rty :-> aty)
                            . addConst repN (aty :-> rty) $ c                           
