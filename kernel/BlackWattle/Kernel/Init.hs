{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}

module BlackWattle.Kernel.Init where

import           Control.Monad.Except
import           Control.Monad.State
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Monoid
import qualified Data.Set as S

import           BlackWattle.Kernel.Types
import           BlackWattle.Kernel.Term
import           BlackWattle.Kernel.Context
import           BlackWattle.Kernel.Theorem
import           BlackWattle.Kernel.World
import           BlackWattle.Kernel.Parser

initWorld :: World
initWorld = World (ContextTree rootContext M.empty)

rootContext = foldr ($) root $ reverse $ run (\n def -> defineConst n (fqnName n ++ "_def") (typeOf def) def) defs
                                         ++ run (\n def -> addAxiom (fqnName n) def) axioms
  where
    parseOne :: (FQName String -> a -> Ctxt -> Ctxt) -> (FQName String, (forall st. WorldM st a)) -> Ctxt -> Ctxt
    parseOne f (n, m) c    = f n (runWorldM [] initWorld m) c

    run f vs               = map (parseOne f) vs

    axioms, defs :: [(FQName String, (forall st. WorldM st Term))]
    axioms = [ (FQN [] "ETA_AX" ,      [termQ| !t : a -> b. (\x : a. t x) = t |] )
             , (FQN [] "SELECT_AX",   [termQ| !P : a -> bool. !x : a. P x --> P (SELECT P) |] )
             , (FQN [] "INFINITY_AX", [termQ| ?f : ind -> ind. ONE_ONE f /\ (NOT (ONTO f)) |] )
             ]

    defs = [ (TrueN,   [termQ| (\p : bool. p) = (\p : bool. p) |])
           , (AndN,    [termQ| \p : bool. \q : bool. (\f : bool -> bool -> bool. f p q) = (\f : bool -> bool -> bool. f TRUE TRUE ) |])
           , (ImplN,   [termQ| \p : bool. \q : bool. (p /\ q) = q |])
           , (AllN,    [termQ| \P : a -> bool. P = (\x. TRUE) |])
           , (ExN,     [termQ| \P. !q. (!x. P x --> q) --> q |])
           , (OrN,     [termQ| \p : bool. \q : bool. !r : bool. (p --> r) --> ((q --> r) --> r) |])
           , (FalseN,  [termQ| !p : bool. p |])
           , (NotN,    [termQ| \p : bool. p --> FALSE |])
           , (Ex1N,    [termQ| \P : a -> bool. (?x : a. P x) /\ (!x : a. !y : a. (P x /\ P y) --> (x = y)) |])
           , (OneOneN, [termQ| \f : a -> b. !x : a. !y : a. (f x = f y) --> (x = y) |])
           , (OntoN,   [termQ| \f : a -> b. !y : b. ?x : a. y = f x |])
           ]
     
    root = Ctxt { _freeTypes      = mempty
                , _freeConstNames = mempty
                , _consts         = M.fromList [(fqnName EqualN, a :-> a :-> boolT), (fqnName SelectN, (a :-> boolT) :-> a)]
                , _types          = M.fromList [(fqnName BoolN, 0), (fqnName IndN, 0), (fqnName FunN, 2) ]
                , _theorems       = mempty
                }
    a = TFree "a"
 
