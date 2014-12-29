{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}

module BlackWattle.Kernel.Types where

import Data.Data

-- FIXME: figure out namespaces
type Name  = String
type TVar  = String
type ConstName = String
type TConstName = String

type ContextName = String

-- | The id '[]' is the root context
type ContextId   = [ContextName]

type TheoremName = String
data FQName a    = FQN { fqnContext :: ContextId
                       , fqnName    :: a
                       }
                   deriving (Eq, Show, Data, Typeable, Ord)

type FullTheoremName = FQName TheoremName
type FullConstName   = FQName ConstName
type FullTConstName  = FQName TConstName

-- * Names

-- FIXME: move
pattern FunN    = FQN [] "fun"
pattern BoolN   = FQN [] "bool"
pattern EqualN  = FQN [] "equal"
pattern IndN    = FQN [] "ind"
pattern TrueN   = FQN [] "TRUE"
pattern AndN    = FQN [] "AND"
pattern ImplN   = FQN [] "IMPL"
pattern AllN    = FQN [] "ALL"
pattern ExN     = FQN [] "EX"
pattern OrN     = FQN [] "OR"
pattern FalseN  = FQN [] "FALSE"
pattern NotN    = FQN [] "NOT"
pattern Ex1N    = FQN [] "EX1"
pattern OneOneN = FQN [] "ONE_ONE" 
pattern OntoN   = FQN [] "ONTO"
pattern SelectN = FQN [] "SELECT"

rootContextId :: ContextId
rootContextId  = []
