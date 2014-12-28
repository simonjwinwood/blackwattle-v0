{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}

module BlackWattle.Kernel.Pretty where

import           Control.Lens
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import qualified Text.PrettyPrint as P
import           Text.PrettyPrint hiding (parens)

import           BlackWattle.Kernel.Types
import           BlackWattle.Kernel.Term
import           BlackWattle.Kernel.Context
import           BlackWattle.Kernel.Theorem
import           BlackWattle.Kernel.World

pparens :: Bool -> Doc -> Doc
pparens b s = if b then P.parens s else s 

prettyTypeSubst :: TypeSubst -> Doc
prettyTypeSubst = vcat . map (\(v, t) -> prettyType v <+> colon <+> prettyType t)

prettyTerm :: Term -> Doc
prettyTerm = go [] False
    where
      go _ _ t@(Free {})     = text $ name t
      go env _ t@(Bound {})  = text $ fst $ env !! depth t
      go _ _ t@(Constant {})    = text $ name t
      go env p t             = let (bs, t', as) = flatten t 
                               in pparens p $ binds bs <+> app (bs ++ env) t' as
      binds []               = empty
      binds bs               = text "\\" <> hsep (map (text . fst) $ reverse bs) <> text "."

      app env (Constant EqualN _) [l, r] = go env True l <+> equals <+> go env True r
      app env (Constant AndN _)   [l, r] = go env True l <+> text "/\\" <+> go env True r
      app env (Constant ImplN _)  [l, r] = go env True l <+> text "-->" <+> go env True r
      app env t                as     = go env False t <+> args env False as

      args _ _ []            = empty 
      args env p as          = hsep $ map (go env True) as
      
prettyType :: Type -> Doc
prettyType = go False
    where
    go _p (TFree v)     = text v
    go _p (TConst c []) = text c
    go p t@(TConst c ts) 
        | Just (ltp, rtp) <- destFunT t = pparens p $ go True ltp <+> text "->" <+> go False rtp
        | otherwise                     = pparens p $ text c <+> (hsep $ map (go True) ts)

prettyContext :: Ctxt -> Doc
prettyContext c = text "freeTypes ="      <+> braces (sep . punctuate comma . map text . S.toList . view freeTypes $ c )
                  $+$ text "freeConstNames =" <+> braces (sep . punctuate comma . map text . S.toList . view freeConstNames $ c )
                  $+$ text "types ="      <+> (vcat . map (\(n, arity) -> text n <+> colon <+> int arity) . M.toList .  view types $ c)
                  $+$ text "consts ="     <+> (vcat . map (\(n, ty) -> text n <+> colon <+> prettyType ty) . M.toList . view consts $ c)
                  $+$ text "theorems ="   <+> (vcat . map (\(n, tm) -> text n <+> colon <+> prettyTerm tm) . M.toList . view theorems $ c)

prettyContextTree :: ContextTree -> Doc
prettyContextTree tree = prettyContext (tree ^. ctContext) -- FIXME

prettyWorld :: World -> Doc
prettyWorld w = prettyContextTree (w ^. contextTree)
