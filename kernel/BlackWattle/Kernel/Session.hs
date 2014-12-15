
module BlackWattle.Kernel.Session where

-- | An 'Interaction a' is a part of session focused on a thing of type a in a context
data Interaction a = Interaction { iContextId :: ContextId
                                 , iFocus     :: a
                                 }

data Session = Session { interactions :: Map InteractionHandle (Interaction ExtThm)
                       , contextTree  :: ContextTree
                       }
