{-# Language PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}

module BlackWattle.Kernel.Theorem where

import           Control.Monad (guard)
import           Data.Function (on)
import           Data.List (any, delete)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Maybe (maybe)
import           Data.Monoid

import           BlackWattle.Kernel.Types
import           BlackWattle.Kernel.Term

-- * Theorem datatype

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

data Theorem st = Theorem { thmDeps    :: Set TheoremName
                          , hypotheses :: HypSet
                          , prop       :: Term } 
           deriving Show

data ExtTheorem = ExtTheorem { extThmDeps :: Map FullTheoremName Term
                             , extTypes   :: Map FullTConstName  Int    -- required?
                             , extConsts  :: Map FullConstName Type
                             , extHyps    :: HypSet
                             , extProp    :: Term
                             }

data CTerm st = CTerm { ctermTerm :: Term, ctermType :: Type }
    deriving Show

newtype CType st = CType { unCType :: Type }
    deriving Show

type CTypeSubst st = [(CType st, CType st)]
type CTermSubst st = [(CTerm st, CTerm st)]

-- | Certified destructors

propC :: Theorem st -> CTerm st
propC thm = CTerm (prop thm) boolT

destCombC :: CTerm st -> Maybe (CTerm st, CTerm st)
destCombC cterm = do l :$ r <- return $ ctermTerm cterm
                     return (CTerm l (typeOf l), CTerm r (typeOf r))

destBinC :: FQName ConstName -> CTerm st -> Maybe (CTerm st, CTerm st)
destBinC n cterm
  | Constant n' ty :$ l :$ r <- ctermTerm cterm, n == n',
    tyl :-> tyr :-> _        <- ty  = Just (CTerm l tyl, CTerm r tyr)
destBinC _ _                        = Nothing

-- | Theorem constructors (meta-axioms and -rules)

mergeHyps :: HypSet -> HypSet -> HypSet
mergeHyps = mappend

emptyTheorem :: Term -> Theorem st
emptyTheorem p = Theorem { thmDeps = mempty, hypotheses = mempty, prop = p }

mergeTheorems :: Theorem st -> Theorem st -> Term -> Theorem st
mergeTheorems thm thm' p =
    Theorem { thmDeps = thmDeps thm `mappend` thmDeps thm' 
            , hypotheses = mergeHyps (hypotheses thm) (hypotheses thm')
            , prop = p
            }

-- Some of these could just be axioms
-- * Meta-axioms

-- | |- l = l
reflexivity :: CTerm st -> Theorem st
reflexivity (CTerm tm ty) = emptyTheorem (mkEq ty tm tm)

-- | A |- l = r
--   B |- r = r'
--  ------------
--  A U B |- l = r'
transitivity :: Theorem st -> Theorem st -> Maybe (Theorem st)
transitivity thm thm' = do (l, r, ty)    <- destEq $ prop thm
                           (l', r', ty') <- destEq $ prop thm'
                           guard (r == l' && ty == ty')
                           return $ mergeTheorems thm thm' $ mkEq ty l r'
-- | A |- f = g
--   B |- x = y
--  ------------
--  A U B |- f x = g y
combCong :: Theorem st -> Theorem st -> Maybe (Theorem st)
combCong thm thm' = do (f, g, ty)    <- destEq $ prop thm
                       (x, y, ty')   <- destEq $ prop thm'
                       (a, r)        <- destFunT ty
                       guard (a == ty')
                       return $ mergeTheorems thm thm' $ mkEq r (f :$ x) (g :$ y)

-- | A |- f = g
--  ------------
--  A |- \x.f = \x.g
lambdaCong :: Name -> CType st -> Theorem st -> Maybe (Theorem st)
lambdaCong n (CType ty) thm = do guard (not freeInHyps)
                                 (f, g, ty')      <- destEq $ prop thm
                                 return $ thm { prop = mkEq (ty :-> ty') (lambda n ty f) (lambda n ty g) }
    where
      freeInHyps = any (vfreeIn (Free n ty)) (hypotheses thm)

-- |
--  ---------------------------
--  |- (\x. f x) y = f[x |-> y]
betaConv :: CTerm st -> Maybe (Theorem st)
betaConv (CTerm tm ty) = do tm' <- beta tm
                            return $ emptyTheorem $ mkEq ty tm tm'

-- |
--  --------
--  [A] |- A
assume :: CTerm st -> Maybe (Theorem st)
assume (CTerm tm ty) = do guard (ty == boolT)
                          return $ Theorem { thmDeps = mempty, hypotheses = [tm], prop = tm }

-- |  A |- l = r
--    B |- l   
--  -------------
--  A U B |- r  
eqMP :: Theorem st -> Theorem st -> Maybe (Theorem st)
eqMP eqthm thm = do (l, r, ty)   <- destEq $ prop eqthm
                    guard (ty == boolT && l == prop thm)
                    return $ mergeTheorems eqthm thm r

-- |         A |- p
--  ----------------------
--   A[x |-> t] |- p[x |-> t]

inst :: CTermSubst st -> CTypeSubst st -> Theorem st -> Maybe (Theorem st)
inst insts instsT thm = do guard $ all (uncurry sameType) insts
                           return $ Theorem { thmDeps = thmDeps thm
                                            , hypotheses = map subst (hypotheses thm)
                                            , prop = subst (prop thm)
                                            }
   where
     subst     = substTermType insts' instsT'
     insts'    = map (\(c, c') -> (ctermTerm c, ctermTerm c')) insts
     instsT'   = map (\(v, c)  -> (unCType v, unCType c)) instsT
     sameType  = (==) `on` ctermType

-- |   A |- p    B |- q
--  ----------------------
--   (A - {q}) U (B - {p}) |- p <--> q
deductAntiSym :: Theorem st -> Theorem st -> Theorem st
deductAntiSym thm1 thm2 = Theorem { thmDeps = thmDeps thm1 `mappend` thmDeps thm2
                                  , hypotheses = mergeHyps (delete (prop thm2) (hypotheses thm1))
                                                           (delete (prop thm1) (hypotheses thm2))
                                  , prop = mkEq boolT (prop thm1) (prop thm2)
                                  }
