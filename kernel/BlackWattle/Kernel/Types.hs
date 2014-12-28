{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}

module BlackWattle.Kernel.Types where

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
                   
type FullTheoremName = FQName TheoremName
type FullConstName   = FQName ConstName
type FullTConstName  = FQName TConstName

-- * Names

-- FIXME: move
pattern FunN   = "fun"
pattern BoolN  = "bool"
pattern EqualN = "equal"
pattern IndN   = "ind"
pattern TrueN  = "TRUE"
pattern AndN   = "AND"
pattern ImplN  = "IMPL"
pattern AllN   = "ALL"
pattern ExN    = "EX"
pattern OrN    = "OR"
pattern FalseN = "FALSE"
pattern NotN   = "NOT"
pattern Ex1N   = "EX1"
pattern OneOneN = "ONE_ONE"
pattern OntoN   = "ONTO"
pattern SelectN = "SELECT"
