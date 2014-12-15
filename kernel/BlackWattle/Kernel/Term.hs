{-# LANGUAGE RankNTypes #-} -- for eqTerm and destAppE
{-# LANGUAGE PatternGuards #-} 
{-# LANGUAGE PatternSynonyms #-}

module BlackWattle.Kernel.Term where

import Data.List (intersperse)
import Data.Maybe (fromMaybe)
import Control.Applicative ( (<*>), (<$>), pure )
    
import Text.PrettyPrint hiding (parens)
import qualified Text.PrettyPrint as P

import BlackWattle.Kernel.Types
import BlackWattle.Util.Update

parens :: Bool -> Doc -> Doc
parens b s = if b then P.parens s else s 

prettyType :: Type -> Doc
prettyType = go False
    where
    go _p (TFree v)     = text v
    go _p (TConst c []) = text c
    go p t@(TConst c ts) 
        | Just (ltp, rtp) <- destFunT t = parens p $ go True ltp <+> text "->" <+> go False rtp
        | otherwise                     = parens p $ text c <+> (hsep $ map (go True) ts)

-- ** Constructing and tearing down types

infixr :->
pattern a :-> r = TConst FunN [a, r]

(~>>) :: [Type] -> Type -> Type
(~>>) as r = foldr (:->) r as

boolT :: Type 
boolT = TConst BoolN []

destFunT :: Type -> Maybe (Type, Type)
destFunT (a :-> r) = Just (a, r)
destFunT _         = Nothing


stripLambda :: Term -> ([(Name, Type)], Term)
stripLambda = go []
    where
    go env t@(Lambda {}) = go ((name t, typ t) : env) (body t)
    go env t             = (env, t)

stripComb :: Term -> (Term, [Term])
stripComb = go []
    where
    go env (l :$ r) = go (r : env) l
    go env t        = (t, env)

flatten :: Term -> ([(Name, Type)], Term, [Term])
flatten t = (bs, t'', as)
    where
    (bs, t')  = stripLambda t
    (t'', as) = stripComb t'

mapTypes :: (Type -> Maybe Type) -> Term -> Term
mapTypes f t = project $ go t
    where
      f' = liftUpdate f
      go, go' :: Term -> Update Term
      go t = go' t <!> t
      go' (Free v ty)        = Free v <$> f' ty
      go' (Const c ty)       = Const c <$> f' ty
      go' (Lambda n ty body) = Lambda n <$> f' ty <*> go body
      go' (l :$ r)           = (:$) <$> go l <*> go r
      go' t                  = pure t

-- ** Type unifiers
type TypeSubst = [(Type, Type)]
type TermSubst = [(Term, Term)]

prettyTypeSubst :: TypeSubst -> Doc
prettyTypeSubst = vcat . map (\(v, t) -> prettyType v <+> colon <+> prettyType t)

addSubst :: Type -> Type -> (TypeSubst -> TypeSubst)
addSubst tv t tu = (tv, t) : tu

emptySubst = []

lookupSubst v tu = lookup v tu

-- | Apply the unifier once, returns the remaining unifiers (which
-- should be applicable to the new term
typeSubst :: TypeSubst -> Type -> Maybe Type
typeSubst tus tv = lookup tv tus

termSubst :: TermSubst -> Term -> Maybe Term
termSubst tus t  = lookup t tus

substTermType :: TermSubst -> TypeSubst -> Term -> Term
substTermType insts instsT = project . go
    where
      fty = liftUpdate (typeSubst instsT)
      f   = liftUpdate (termSubst insts)
      go, go' :: Term -> Update Term
      go t = go' t <!> t
      -- Do the term substitution first and then the type subst if it doesn't do anything
      go' t@(Free v ty)      = f t <||> (Free v <$> fty ty)
      go' (Const c ty)       = Const c <$> fty ty
      go' (Lambda n ty body) = Lambda n <$> fty ty <*> go body
      go' (l :$ r)           = (:$) <$> go l <*> go r
      go' t                  = pure t

prettyTerm :: Term -> Doc
prettyTerm = go [] False
    where
      go _ _ t@(Free {})     = text $ name t
      go env _ t@(Bound {})  = text $ fst $ env !! depth t
      go _ _ t@(Const {})    = text $ name t
      go env p t             = let (bs, t', as) = flatten t 
                               in parens p $ binds bs <+> app (bs ++ env) t' as
      binds []               = empty
      binds bs               = text "\\" <> hsep (map (text . fst) $ reverse bs) <+> text "->"

      app env (Const EqualN _) [l, r] = go env True l <+> equals <+> go env True r
      app env (Const AndN _)   [l, r] = go env True l <+> text "/\\" <+> go env True r
      app env (Const ImplN _)  [l, r] = go env True l <+> text "-->" <+> go env True r
      app env t                as     = go env False t <+> args env False as

      args _ _ []            = empty 
      args env p as          = hsep $ map (go env True) as



-- ** Constructors and destructors

-- | Abstract out a term

abstract :: Term -> Term -> Term
abstract tm = go 0 
    where
    go d t 
        | t == tm   = Bound d
        | otherwise = go' d t
    go' d (Lambda n tp t)  = Lambda n tp (go (d + 1) t)
    go' d (t :$ t')       = (go d t) :$ (go d t')
    go' _ t                = t -- Bound, Const, and Var

-- | Smart constructor for lambda.  Note that this means that the name
-- of a var includes its type.

lambda :: Name -> Type -> Term -> Term
lambda x tp t = Lambda x tp (abstract (Free x tp) t)

mkEq :: Type -> Term -> Term -> Term
mkEq ty l r = (Const EqualN (ty :-> ty :-> boolT) :$ l :$ r)

destEq :: Term -> Maybe (Term, Term, Type)
destEq (Const EqualN ty :$ l :$ r)
    | Just (ty, _) <- destFunT ty        = Just (l, r, ty) 
destEq _                                 = Nothing

-- ** Free terms etc.

vfreeIn :: Term -> Term -> Bool
vfreeIn tm tm'@(Free {})  = tm == tm'
vfreeIn tm (Lambda _ _ t) = vfreeIn tm t
vfreeIn tm (tf :$ ta)     = vfreeIn tm tf || vfreeIn tm ta
vfreeIn _  _              = False

-- ** Substitution and reduction

-- | See "Proof Pearl: de Bruijn Terms Really Do Work" by Michael
-- Norrish and Rene Vestergaard and related papers

subst :: Term -> Term -> Term
subst tm = go 0
    where
    -- There are d + 1 binders outside t, so we need to lift any binders in 
    -- tm by d, noting that subst expects one Lambda to be removed from the context.
    go d t@(Bound d') 
        | d < d'         = Bound (d' - 1)
        | d == d'        = liftBound d 0 tm -- rename bound vars, de Bruijn style
        | otherwise      = t
    go d (t :$ t')       = (go d t) :$ (go d t')
    go d (Lambda n tp t) = Lambda n tp (go (d + 1) t)
    go _ t               = t

liftBound :: Int -> Int -> Term -> Term
liftBound = go
    where
    go m d t@(Bound d')
        | d' < d           = Bound (d' + m)
        | otherwise        = t
    go m d (t :$ t')       = (go m d t) :$ (go m d t')
    go m d (Lambda n tp t) = Lambda n tp (go (m + 1) (d + 1) t)
    go _ _ t               = t

-- The argument should not have any unbound Bound terms.

-- | Head normal form
hnf :: Term -> Term
hnf (t :$ t') = case hnf t of
                   Lambda _ _ tf -> subst t' tf 
                   reduct        -> reduct :$ t'
hnf t          = t

-- | Completely normalise a term
betaNormalise :: Term -> Term
betaNormalise (t :$ t')      = case betaNormalise t of
                                 Lambda _ _ body -> subst (betaNormalise t') body
                                 tb              -> tb :$ (betaNormalise t')
betaNormalise (Lambda n tp t) = Lambda n tp (betaNormalise t)
betaNormalise t               = t

-- | Reduce the outermost redex, assuming we have one.
beta :: Term -> Maybe Term
beta ((Lambda _ _ b) :$ t)      = Just $ subst t b
beta t                          = Nothing


prettyCTerm (CTerm tm tp) = 
    prettyTerm tm <+> colon <+> prettyType tp

ctermTerm :: CTerm st -> Term
ctermTerm (CTerm tm _) = tm

ctermType :: CTerm st -> Type
ctermType (CTerm _ ty) = ty

-- Well-typed terms only!
typeOf :: Term -> Type
typeOf = go []
  where
    go _   (Free _ ty)  = ty
    go env (Bound n)
      | n < length env  = env !! n
      | otherwise       = error "Out of bound variable"
    go _   (Const _ ty) = ty
    go env (Lambda _ ty t) = ty :-> go (ty : env) t
    go env (l :$ _)     = case go env l of
                            _ :-> ty -> ty
                            _        -> error "Not a function type"


{-

newtype EqTerm a = EqTerm { unEqTerm :: Term }

eqTerm :: Term -> (forall s. EqTerm s)
eqTerm = EqTerm

destAppE :: EqTerm s -> (EqTerm t -> EqTerm t' -> (forall t t'. EqTerm t -> EqTerm t' -> EqTerm s) -> a) -> Maybe a
destAppE (EqTerm (App t t'))  f = Just (f (eqTerm t) (eqTerm t') (\t t' -> eqTerm (App (unEqTerm t) (unEqTerm t'))))
destAppE _ _                    = Nothing
-}
