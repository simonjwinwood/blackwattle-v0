{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}

-- A simple parser for making writing some terms nicer.  Only in the kernel for bootstrapping ...

module BlackWattle.Kernel.Parser (termQ, typeQ, debugTermQ) where

import           Control.Applicative ( (<$>), (<*>) )
import           Control.Lens
import           Control.Monad.Identity
import           Control.Monad.State
import           Data.Data
import           Data.List (elemIndex, elem)
import           Data.Maybe (fromMaybe)
import qualified Language.Haskell.TH as TH
import           Language.Haskell.TH.Quote

import           Text.Parsec

import           BlackWattle.Kernel.Context (types, consts)
import           BlackWattle.Kernel.Term
import           BlackWattle.Kernel.Types
import           BlackWattle.Kernel.World

-- Might not need the intermediate types?
data TypeTree = TVarQ String
              | TAppQ TypeTree TypeTree
              | TMetaQ String
              | TMetaInstQ Type
              deriving (Show, Typeable, Data)

data TermTree = VarQ String
              | LambdaQ String TypeTree TermTree
              | AppQ TermTree TermTree
              | MetaQ String
              | MetaInstQ Term
              deriving (Show, Typeable, Data)

-- * Type elaboration

-- FIXME: move

unknownType :: Type
unknownType = TFree ""

unknownTypeQ :: TypeTree
unknownTypeQ = TVarQ ""

-- Might get strange results if there are frees (unintentionally) in common.
unifyTypes :: Type -> Type -> TypeSubst -> Maybe TypeSubst
unifyTypes ty ty' subst = execStateT (go ty ty') subst
  where
    expand t@(TFree v) = do m_t <- gets (lookupSubst t)
                            return $ fromMaybe t m_t
    expand t           = return t

    go l r  = do l' <- expand l
                 r' <- expand r
                 go' l' r'
    
    go' l@(TFree v)    r                     = modify (addTypeSubst l r) 
    go' l              r@(TFree v)           = go' r l
    go' (TConst c tys) (TConst c' tys') -- assumes that length tys == length tys'
      | c /= c'                              = fail $ "No unifier for " ++ show c ++ " and " ++ show c'
      | otherwise                            = zipWithM_ go tys tys'

-- resolves any type variables such that the term will type check.  Fails
-- if there is no possible assignment to the type variables.
elaborate :: Term -> Maybe Term
elaborate tm = finalSubst <$> runStateT (go [] tm) (emptySubst, freshTVars')
  where
    freeTVars   = freeTypesInTerm tm
    freshTVars' = filter (`notElem` freeTVars) freshTVars

    fresh' :: Monad m => StateT (a, [String]) m String
    fresh' = _2 %%= \(v : vs) -> (v, vs)
    
    substTypeInTerm = substTermType emptySubst
    finalSubst ((tm', _), (instsT, _)) = substTypeInTerm instsT tm'

    go :: [Type] -> Term -> StateT (TypeSubst, [String]) Maybe (Term, Type)    
    go _env t@(Free _ ty)     = return (t, ty)
    go env t@(Bound n)
      | n < length env        = return (t, env !! n)
      | otherwise             = fail "Unknown binder"
    go _env t@(Constant _ ty) = return (t, ty)
    go env (Lambda n ty b)   = do (body', bodyTy) <- go (ty : env) b
                                  return (Lambda n ty body', ty :-> bodyTy)
    go env (l :$ r)          = do (l', lty) <- go env l
                                  (r', rty) <- go env r
                                  resTy     <- TFree <$> fresh'
                                  instsT'   <- gets fst >>= lift . unifyTypes lty (rty :-> resTy)
                                  _1 %= const instsT'
                                  -- OK that this is a fresh var here, will be expanded later
                                  return (l' :$ r', resTy) 




-- * Translation to Term/Type

freshTVars :: [String]
freshTVars = map ((++) "a" . show) [1..] -- we assume a1, a2, ... are free.

fresh :: Monad m => StateT [String] m String
fresh = state (\(v:vs) -> (v, vs))

renameT :: (Monad m, Functor m) => Type -> StateT [String] m Type
renameT ty = do let freeTs = freeTypesInType ty
                instsT <- mapM (\n -> (TFree n, ) . TFree <$> fresh) freeTs
                return $ substType instsT ty

typeTreeToType :: TypeTree -> WorldM st Type
typeTreeToType tree = evalStateT (typeTreeToType' tree) freshTVars

typeTreeToType' :: TypeTree -> StateT [String] (WorldT st Identity) Type
typeTreeToType' tree = go [] tree
  where
   go :: forall st. [Type] -> TypeTree -> StateT [String] (WorldT st Identity) Type
   go _targs (TVarQ "") = TFree <$> fresh
   go targs (TVarQ v)   = do m_arity <- lift (resolveType v)
                             case m_arity of
                                Nothing
                                  | null targs -> return $ TFree v
                                  | otherwise  -> error $ "Type args to a type variable: " ++ v
                                Just (cid, n)
                                  | length targs == n -> return $ TConst (FQN cid v) targs
                                  | otherwise         -> error $ "Wrong no. args to " ++ v                              
   go targs (TAppQ l r)    = do r' <- go [] r
                                go (r' : targs) l
   go _     (TMetaInstQ t) = return t
   go _     (TMetaQ _)     = error "TMeta"

-- FIXME: We only allow closed terms currently ...
-- FIXME: cterm?
   
-- When we see an explicit type variable like on a Lambda, we leave
-- it, but when we see a polymorphic constant we need to instantiate
-- type vars with fresh variables.

termTreeToTerm :: TermTree -> WorldM st Term
termTreeToTerm t = evalStateT (go [] t) freshTVars
  where
    go env (VarQ v) 
      | Just n <- elemIndex v env = return $ Bound n
      | otherwise  = do m_type <- lift $ resolveConst v
                        case m_type of
                          Nothing         -> Free v . TFree <$> fresh
                          Just (cid, ty) -> Constant (FQN cid v) <$> renameT ty
    go env (LambdaQ n ty tm) = Lambda n <$> typeTreeToType' ty <*> go (n : env) tm
    go env (AppQ l r)        = (:$) <$> go env l <*> go env r
    go _   (MetaInstQ t)     = return t
    go _   (MetaQ _)         = error $ "Meta"

type ParserM a = Parsec String () a

termQ :: QuasiQuoter
termQ = QuasiQuoter { quoteExp = \s -> [| termTreeToTerm $( quotePExp termP antiExp s ) |]
                    , quotePat = undefined -- termPat
                    , quoteDec = undefined
                    , quoteType = undefined 
                    }

debugTermQ :: QuasiQuoter
debugTermQ = QuasiQuoter { quoteExp = quotePExp termP antiExp
                         , quotePat = undefined -- termPat
                         , quoteDec = undefined
                         , quoteType = undefined 
                         }

typeQ :: QuasiQuoter
typeQ = QuasiQuoter { quoteExp = \s -> [| typeTreeToType $( quotePExp typeP antiTExp s ) |]
                    , quotePat = undefined -- termPat
                    , quoteDec = undefined
                    , quoteType = undefined 
                    }

quotePExp p q s =  do loc <- TH.location
                      let pos = (TH.loc_filename loc,
                                 fst (TH.loc_start loc),
                                 snd (TH.loc_start loc))
                      v <- withParser p pos s
                      dataToExpQ (const Nothing `extQ` q) v

antiTExp  (TMetaQ v)   = Just [| TMetaInstQ $(TH.varE (TH.mkName v)) |]
antiTExp  _            = Nothing

antiExp  (MetaQ v)     = Just [| MetaInstQ $(TH.varE (TH.mkName v)) |]
antiExp  _             = Nothing

-- * Parser

-- clag from https://www.haskell.org/haskellwiki/Quasiquotation
withParser :: Monad m => ParserM a -> (String, Int, Int) -> String -> m a
withParser p_a (file, line, col) s =
    case runParser p () "" s of
      Left err  -> fail $ show err
      Right e   -> return e
  where
    p = do  pos <- getPosition
            setPosition $
              (flip setSourceName) file $
              (flip setSourceLine) line $
              (flip setSourceColumn) col $
              pos
            spaces
            e <- p_a
            spaces
            eof
            return e


-- * Parsers

-- more from ibid
lexeme p     = do { x <- p; spaces; return x }
symbol name  = lexeme (string name)
parens p     = between (symbol "(") (symbol ")") p

idchar  = lower <|> char '_' <|> upper <|> digit <|> char '\''

ident  :: ParserM String
ident  =  many1 idchar

typeP, tappP, nonFunT :: ParserM TypeTree
typeP   = tappP `chainr1` (symbol "->" >> return (\l r -> TAppQ (TAppQ (TVarQ (fqnName FunN)) l) r))
tappP  = foldl1 TAppQ <$> many1 nonFunT
nonFunT = parens typeP <|> tmetaP <|> lexeme (TVarQ <$> ident)
tmetaP  = lexeme (do string "$"
                     TMetaQ <$> ident
                  )
        
termP, lambdaP  :: ParserM TermTree

infixes = [ ("=", EqualN)
          , ("-->", ImplN)
          , ("/\\", AndN)
          , ("\\/", OrN)
          ]

termP    = do l <- lamOrApp
              (do n <- choice (map (\(sym, n) -> symbol sym >> return n) infixes)
                  r <- lamOrApp
                  return (AppQ (AppQ (VarQ (fqnName  n)) l) r)) <|> return l

lamOrApp = lambdaP <|> allP <|> exP <|> (foldl1 AppQ <$> many1 nonLamP)
nonLamP = parens termP <|> metaP <|> lexeme (VarQ <$> ident)

binderP start f = do start
                     v <- lexeme ident
                     t <- option unknownTypeQ (symbol ":" >> typeP)
                     symbol "."
                     body <- termP
                     return (f v t body)

lambdaP = binderP (symbol "\\") LambdaQ
allP    = binderP (symbol "!") (\n ty t -> AppQ (VarQ (fqnName AllN)) (LambdaQ n ty t))
exP     = binderP (symbol "?") (\n ty t -> AppQ (VarQ (fqnName ExN)) (LambdaQ n ty t))

metaP  = lexeme (do string "$"
                    MetaQ <$> ident
                 )

-- clag
extQ :: ( Typeable a
        , Typeable b
        )
     => (a -> q)
     -> (b -> q)
     -> a
     -> q
extQ f g a = maybe (f a) g (cast a)

