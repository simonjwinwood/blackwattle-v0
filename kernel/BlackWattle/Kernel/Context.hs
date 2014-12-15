{-# LANGUAGE RankNTypes #-}

{- Context.hs --- theorem contexts

-}

module BlackWattle.Kernel.Context where

import           Control.Monad.Except
import           Control.Monad.State
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Monoid
import qualified Data.Set as S
import qualified Text.PrettyPrint as P
import           Text.PrettyPrint hiding (parens)

import           BlackWattle.Kernel.Types
import           BlackWattle.Kernel.Term
import           BlackWattle.Kernel.Theorem

rootContextId :: ContextId
rootContextId  = []

-- returns the deepest context first (reverse search order)
contextTreePath :: ContextId -> ContextTree -> Maybe [Context]
contextTreePath = go []
  where
   go acc cid tree = let acc' = ctContext tree : acc
                     in case cid of
                          []         -> return acc'
                          (c : cid') -> go acc' cid' =<< M.lookup c (ctChildren tree)

-- FIXME: use fully qualified names?  This just finds the first ...
lookupTheorem :: TheoremName -> ContextM st (Maybe (Theorem st))
lookupTheorem thmN = ContextM $ gets (msum . map (findIt . theorems))
  where
    findIt m = do tm <- M.lookup thmN m
                  return $ Theorem { thydeps = S.singleton thmN
                                   , hypotheses = mempty
                                   , prop = tm }


constType :: Const -> ContextM st (Maybe Type)
constType constN = ContextM $ gets (msum . map (M.lookup constN . consts))

typeArity :: TConst -> ContextM st (Maybe Int)
typeArity tconstN = ContextM $ gets (msum . map (M.lookup tconstN . types))

maybeToError :: MonadError e m => e -> Maybe a -> m a
maybeToError e v = case v of
                     Nothing -> throwError e
                     Just v' -> return v'

-- | Internal only!
runContextM :: [Context] -> ContextM st a -> a
runContextM ctxt m = evalState (unContextM m) ctxt

withContext :: ContextId -> (forall st. ContextM st a) -> BWM a
withContext cid m = BWM $ do ctxt <- maybeToError "Not found" =<< gets (contextTreePath cid)
                             return $ evalState (unContextM m) ctxt

primAddTheorem :: TheoremName -> Term -> Context -> Context
primAddTheorem thmN tm ctxt = ctxt { theorems = M.insert thmN tm $ theorems ctxt }

primAddConst :: Const -> Type -> Context -> Context
primAddConst nm ty ctxt = ctxt { consts = M.insert nm ty $ consts ctxt }

primDefineConst :: Const -> Type -> Term -> Context -> Context
primDefineConst nm ty def ctxt = primAddTheorem (nm ++ "_def")
                                                (mkEq ty (Const nm ty) def)
                                                (primAddConst nm ty ctxt)

-- * Pretty printing

prettyContext :: Context -> Doc
prettyContext c = text "freeTypes ="      <+> braces (sep . punctuate comma . map text . S.toList . freeTypes $ c )
                  $+$ text "freeConsts =" <+> braces (sep . punctuate comma . map text . S.toList . freeConsts $ c )
                  $+$ text "types ="      <+> (vcat . map (\(n, arity) -> text n <+> colon <+> int arity) . M.toList . types $ c)
                  $+$ text "consts ="     <+> (vcat . map (\(n, ty) -> text n <+> colon <+> prettyType ty) . M.toList . consts $ c)
                  $+$ text "theorems ="   <+> (vcat . map (\(n, tm) -> text n <+> colon <+> prettyTerm tm) . M.toList . theorems $ c)


  -- where

    -- data Context = Context { freeTypes   :: Set TConst            -- ^ Those types which are free
    --                        , freeConsts  :: Set Const             -- ^ Those consts which are free 
    --                        , types       :: Map TConst  Int       -- ^ All types and their 
    --                        , consts      :: Map Const   Type      -- ^ All consts and their types
    --                        , theorems    :: Map TheoremName Term  -- ^ Theorems in context
    --                        }
