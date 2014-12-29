{-# LANGUAGE RankNTypes #-}

module BlackWattle.Kernel.Session where

import           Control.Applicative ( (<*>), (<$>), pure )
import           Control.Monad (join)
import           Control.Monad.Trans (lift)
import           Data.IORef
import           Data.Maybe
import           System.IO.Unsafe

import           BlackWattle.Kernel.Init
import           BlackWattle.Kernel.Parser
import           BlackWattle.Kernel.Pretty
import           BlackWattle.Kernel.Term
import           BlackWattle.Kernel.Theorem (Theorem, CTerm (..), ExtTheorem (..))
import qualified BlackWattle.Kernel.Theorem as Thm
import           BlackWattle.Kernel.Types
import           BlackWattle.Kernel.World

-- | Lifting from Theorem to fail

maybeToFail :: Monad m => Maybe a -> m a
maybeToFail = maybe (fail "Nothing") return

-- lift to Monad m from Maybe
destBinC :: Monad m => FQName ConstName -> Theorem st -> m (CTerm st, CTerm st)
destBinC n thm = maybeToFail $ Thm.destBinC n $ Thm.propC thm

destCombC :: Monad m => CTerm st -> m (CTerm st, CTerm st)
destCombC = maybeToFail . Thm.destCombC

-- | State

worldState = unsafePerformIO (newIORef initWorld)

currentThm :: IORef ExtTheorem
currentThm = unsafePerformIO (newIORef undefined)

ppWorld = do w <- readIORef worldState
             print $ prettyWorld w

finish m_ethm = case m_ethm of
                  Nothing    -> putStrLn "Error"
                  Just ethm' -> do writeIORef currentThm ethm'
                                   print $ prettyExtTheorem ethm'

prove :: (forall st. WorldM st Term) -> IO ()
prove m = do w <- readIORef worldState
             let m_ethm  = runWorldM [] w (do tm  <- (m >>= certifyTerm)
                                              m_thm <- return $ Thm.assume =<< tm
                                              case m_thm of
                                                Nothing  -> return Nothing
                                                Just thm -> Just <$> extern thm)
             finish m_ethm

-- unfold :: TheoremName -> IO ()
-- unfold thmN = tactic' $ \goal -> do undefined

-- | x = y ==> y = x
symmetry :: Monad m => Theorem st -> m (Theorem st)
symmetry thm = do (l, _) <- destBinC EqualN thm
                  let lthm = Thm.reflexivity l
                  (eq_at_ty, _) <- destCombC (Thm.propC thm) >>= destCombC . fst
                  maybeToFail $ do l_eq_eq_r_eq <- Thm.combCong (Thm.reflexivity eq_at_ty) thm
                                   ll_eq_rl     <- Thm.combCong l_eq_eq_r_eq lthm
                                   Thm.eqMP ll_eq_rl lthm

tactic' :: (forall st. Theorem st -> WorldT st Maybe (Theorem st)) -> IO ()
tactic' f = do ethm <- readIORef currentThm
               w    <- readIORef worldState
               let m_ethm = runWorldT [] w (go ethm)
               finish m_ethm
  where
    go ethm = do m_thm <- intern ethm
                 thm   <- lift m_thm >>= f
                 extern thm

tactic :: (forall st. Theorem st -> WorldM st (Theorem st)) -> IO ()
tactic f = do ethm <- readIORef currentThm
              w    <- readIORef worldState
              let m_ethm = runWorldM [] w (go ethm)
              finish m_ethm
  where
    go ethm = do m_thm <- intern ethm
                 case m_thm of
                   Nothing  -> return Nothing
                   Just thm -> f thm >>= fmap Just . extern

-- | an 'Interaction a' is a part of session focused on a thing of type a in a context
-- data Interaction a = Interaction { iContextId :: ContextId
--                                  , iFocus     :: a
--                                  }

-- data Session = Session { interactions :: Map InteractionHandle (Interaction ExtThm)
--                        , contextTree  :: ContextTree
--                        }
