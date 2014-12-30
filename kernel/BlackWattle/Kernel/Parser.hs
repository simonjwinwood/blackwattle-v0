{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}

-- A simple parser for making writing some terms nicer.  Only in the kernel for bootstrapping ...

module BlackWattle.Kernel.Parser (termQ, typeQ, debugTermQ, ctermQ) where

import           Control.Applicative ( (<$>), (<*>) )
import           Control.Lens
import           Control.Monad.Identity
import           Control.Monad.State
import           Data.Data
import           Data.List (elemIndex, elem)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (fromMaybe)
import qualified Language.Haskell.TH as TH
import           Language.Haskell.TH.Quote

import           Text.Parsec

import           BlackWattle.Kernel.Context (types, consts)
import           BlackWattle.Kernel.Term
import           BlackWattle.Kernel.Types
import           BlackWattle.Kernel.World
import           BlackWattle.Kernel.Pretty

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
elaborate :: Term ->  Maybe Term
elaborate tm = finalSubst <$> runStateT (go [] tm) (emptySubst, freshTVars')
  where
    freeTVars   = freeTypesInTerm tm
    freshTVars' = filter (`notElem` freeTVars) freshTVars
    
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
                                  resTy     <- TFree <$> fresh _2
                                  instsT    <- gets fst
                                  let lty' = (rty :-> resTy)
                                      res = unifyTypes lty lty' instsT
                                  instsT' <- maybe (error $ "Couldn't unify " ++ show (prettyType lty) ++ " and " ++ show (prettyType lty')) return res
                                  -- instsT'   <- gets fst >>= lift . unifyTypes lty (rty :-> resTy)
                                  _1 %= const instsT'
                                  -- OK that this is a fresh var here, will be expanded later
                                  return (l' :$ r', resTy) 




-- * Translation to Term/Type

freshTVars :: [String]
freshTVars = map ((++) "a" . show) [1..] -- we assume a1, a2, ... are free.

fresh :: MonadState a m => Lens' a [String] -> m String
fresh l = l %%= (\(v:vs) -> (v, vs))

renameT :: (MonadState a m, Functor m) => Lens' a [String] -> Type -> m Type
renameT l ty = do let freeTs = freeTypesInType ty
                  instsT <- mapM (\n -> (TFree n, ) . TFree <$> fresh l) freeTs
                  return $ substType instsT ty

typeTreeToType :: TypeTree -> WorldM st Type
typeTreeToType tree = evalStateT (typeTreeToType' id tree) freshTVars

typeTreeToType' :: Lens' a [String]  -> TypeTree -> StateT a (WorldT st Identity) Type
typeTreeToType' l tree = go [] tree
  where
   -- go :: forall st. [Type] -> TypeTree -> StateT a (WorldT st Identity) Type
   go _targs (TVarQ "") = TFree <$> fresh l
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
termTreeToTerm t = (\tm -> fromMaybe (error $ "Couldn't elaborate " ++ show tm) (elaborate tm)) <$> evalStateT (go [] t) (M.empty, freshTVars)
  where
    -- keeps track of frees we have already seen so we get the same type for both ... not absolutely
    -- required, but otherwise might be confusing.
    freshMaybe n = state (\st@(seen, freshTs@(v:vs)) -> case M.lookup n seen of
                                                            Nothing -> (v, (M.insert n v seen, vs))
                                                            Just v' -> (v', st)
                                                           )

    go env (VarQ v) 
      | Just n <- elemIndex v env = return $ Bound n
      | otherwise  = do m_type <- lift $ resolveConst v
                        case m_type of
                          Nothing         -> Free v . TFree <$> freshMaybe v
                          Just (cid, ty)  -> Constant (FQN cid v) <$> renameT _2 ty
    go env (LambdaQ n ty tm) = Lambda n <$> typeTreeToType' _2 ty <*> go (n : env) tm
    go env (AppQ l r)        = (:$) <$> go env l <*> go env r
    go _   (MetaInstQ t)     = return t
    go _   (MetaQ _)         = error $ "Meta"

type ParserM a = Parsec String () a

ctermQ :: QuasiQuoter
ctermQ = QuasiQuoter { quoteExp = \s -> [| termTreeToTerm $( quotePExp termP antiExp s ) >>= intern |]
                     , quotePat = undefined -- termPat
                     , quoteDec = undefined
                     , quoteType = undefined 
                     }

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

