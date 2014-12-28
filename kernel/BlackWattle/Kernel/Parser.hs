{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}

-- A simple parser for making writing some terms nicer.  Only in the kernel for bootstrapping ...

module BlackWattle.Kernel.Parser (termQ, typeQ) where

import           Control.Applicative ( (<$>), (<*>) )
import           Data.Data
import           Data.List (elemIndex)
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

-- * Translation to Term/Type

typeTreeToType :: TypeTree -> WorldM st Type
typeTreeToType tree = go [] tree
  where
   go targs (TVarQ v) = do m_arity <- resolveType v
                           case m_arity of
                              Nothing
                                | null targs -> return $ TFree v
                                | otherwise  -> error $ "Type args to a type variable: " ++ v
                              Just (_cid, n)
                                | length targs == n -> return $ TConst v targs
                                | otherwise         -> error $ "Wrong no. args to " ++ v                              
   go targs (TAppQ l r)    = do r' <- go [] r
                                go (r' : targs) l
   go _     (TMetaInstQ t) = return t
   go _     (TMetaQ _)     = error "TMeta"

-- FIXME: We only allow closed terms currently ...
-- FIXME: cterm?
termTreeToTerm :: TermTree -> WorldM st Term
termTreeToTerm t = go [] t
  where
    go env (VarQ v) 
      | Just n <- elemIndex v env = return $ Bound n
      | otherwise  = do m_type <- resolveConst v
                        case m_type of
                          Nothing         -> error $ "Free constant " ++ v ++ " " ++ show t
                          Just (_cid, ty) -> return $ Constant v ty
    go env (LambdaQ n ty tm) = Lambda n <$> typeTreeToType ty <*> go (n : env) tm
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
typeP   = tappP `chainr1` (symbol "->" >> return (\l r -> TAppQ (TAppQ (TVarQ FunN) l) r))
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
                  return (AppQ (AppQ (VarQ n) l) r)) <|> return l

lamOrApp = lambdaP <|> allP <|> exP <|> (foldl1 AppQ <$> many1 nonLamP)
nonLamP = parens termP <|> metaP <|> lexeme (VarQ <$> ident)

binderP start f = do start
                     v <- lexeme ident
                     symbol ":"
                     t <- typeP
                     symbol "."
                     body <- termP
                     return (f v t body)

lambdaP = binderP (symbol "\\") LambdaQ
allP    = binderP (symbol "!") (\n ty t -> AppQ (VarQ AllN) (LambdaQ n ty t))
exP     = binderP (symbol "?") (\n ty t -> AppQ (VarQ ExN) (LambdaQ n ty t))

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

