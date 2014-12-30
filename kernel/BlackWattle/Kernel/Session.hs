{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuasiQuotes #-}

module BlackWattle.Kernel.Session where

import           Control.Applicative ( (<*>), (<$>), pure )
import           Control.Lens
import           Control.Monad (join)
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.Trans (lift)
import           Data.Monoid
import           Data.IORef
import           Data.Maybe
import           System.IO.Unsafe
import           Text.PrettyPrint (text, Doc)

import           BlackWattle.Kernel.Init
import           BlackWattle.Kernel.Parser
import           BlackWattle.Kernel.Pretty
import           BlackWattle.Kernel.Term
import           BlackWattle.Kernel.Theorem (Theorem, CTerm (..), ExtTheorem (..), CType (..))
import qualified BlackWattle.Kernel.Theorem as Thm
import           BlackWattle.Kernel.Types
import           BlackWattle.Kernel.World
import           BlackWattle.Kernel.Parser

type Tactic = (forall st. Theorem st -> WorldT st Maybe (Theorem st))

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
currentThm = unsafePerformIO (newIORef $ error "No proof started")

ppWorld = do w <- readIORef worldState
             print $ prettyWorld w

finish m_ethm = case m_ethm of
                  Nothing    -> putStrLn "Error"
                  Just ethm' -> do writeIORef currentThm ethm'
                                   print $ prettyExtTheorem ethm'

prove :: (forall st. WorldM st Term) -> IO ()
prove m = do w <- readIORef worldState
             let m_ethm  = runWorldT [] w (do tm  <- liftMaybe (m >>= certifyTerm)
                                              thm <- lift $ Thm.assume tm
                                              extern thm)
             finish m_ethm

-- turns F t into G t where f : F = G

newtype Conv = Conv { runConv :: forall st. CTerm st -> WorldT st Maybe (Theorem st) }

allConv :: Conv
allConv = Conv $ return .Thm.reflexivity

-- | sequencing semantics
instance Monoid Conv where
  mempty = allConv
  mappend c1 c2 = Conv $ \ctm -> do thm1     <- runConv c1 ctm
                                    (_, rhs) <- destBinC EqualN thm1
                                    thm2 <- runConv c2 rhs
                                    lift $ Thm.transitivity thm1 thm2

ratorConv :: Conv -> Conv
ratorConv cnv = Conv $ \ctm -> do (l, r) <- destCombC ctm
                                  lThm   <- runConv cnv l -- l == l'
                                  lift $ Thm.combCong lThm (Thm.reflexivity r)

unfoldConv :: TheoremName -> Conv
unfoldConv thmN = Conv $ \ctm -> do defThm <- liftMaybe $ resolveTheorem thmN
                                    (l, _) <- destBinC EqualN defThm
                                    instsT <- lift $ ctermType ctm `isTyInstOf` ctermType l
                                    -- FIXME
                                    lift $ Thm.inst emptySubst (map (\(ty, ty') -> (CType ty, CType ty')) instsT) defThm

conv :: Conv -> Tactic
conv cnv goal = do thm <-runConv cnv (Thm.propC goal)
                   lift $ Thm.eqMP thm goal

betaConv :: Conv
betaConv = Conv $ lift . Thm.betaConv

-- | x = y ==> y = x
symmetry :: Theorem st -> WorldT st Maybe (Theorem st)
symmetry thm = do (l, _) <- destBinC EqualN thm
                  let lthm = Thm.reflexivity l
                  (eq_at_ty, _) <- destCombC (Thm.propC thm) >>= destCombC . fst
                  lift $ do l_eq_eq_r_eq <- Thm.combCong (Thm.reflexivity eq_at_ty) thm
                            ll_eq_rl     <- Thm.combCong l_eq_eq_r_eq lthm
                            Thm.eqMP ll_eq_rl lthm

-- * True

trueI :: WorldT st Maybe (Theorem st)
trueI = do p_p <- Thm.reflexivity <$> liftMaybe [ctermQ| \p : bool. p |]
           trueDefS <- symmetry =<< liftMaybe (resolveTheorem "TRUE_def")
           lift $ Thm.eqMP trueDefS p_p

eqTrueE :: Tactic
eqTrueE thm = maybeToFail =<< Thm.eqMP <$> symmetry thm  <*> trueI

dtactic :: (a -> Doc) ->  (forall st. Theorem st -> WorldT st Maybe a) -> IO ()
dtactic pp f = do ethm <- readIORef currentThm
                  w    <- readIORef worldState
                  let m_ethm = runWorldT [] w (go ethm)
                  print $ maybe (text "ERROR") pp m_ethm
  where
    go ethm = do m_thm <- intern ethm
                 lift m_thm >>= f
                 
dconv :: Conv -> IO ()
dconv c = dtactic prettyExtTheorem (\goal -> conv c goal >>= extern)


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
