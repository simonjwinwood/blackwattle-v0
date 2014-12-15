{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

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
import           BlackWattle.Kernel.Parser

rootContext = go root defs
  where
    go c []               = c
    go c ((n, m) : defs') = let def = runContextM [c] m
                                c'  =  primDefineConst n (typeOf def) def c
                            in go c' defs'

    defs = [ (TrueN, [termQ| (\p : bool -> p) = (\p : bool -> p) |])
           , (AndN,  [termQ| \p : bool -> \q : bool -> (\f : (bool -> bool -> bool) -> f p q) = (\f : (bool -> bool -> bool) -> f TRUE TRUE ) |])
           , (ImplN, [termQ| \p : bool -> \q : bool -> AND p q = q |])
           
           ]
    root = Context { freeTypes  = mempty
                   , freeConsts = mempty
                   , consts     = M.fromList [(EqualN, a :-> a :-> boolT)]
                   , types      = M.fromList [(BoolN, 0), (IndN, 0), (FunN, 2) ]
                   , theorems   = mempty
                   }
    a = TFree "a"

