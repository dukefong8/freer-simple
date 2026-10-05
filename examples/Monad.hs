{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
module Monad where

import Control.Category (Category ((.)), id)
import Prelude hiding (id, (.))

-----------------------------------------------------------------------------
-- Free Monad

data Free f a
  = Pure a
  | Join (f (Free f a))
  deriving (Functor)

instance Functor f => Applicative (Free f) where
  pure = Pure
  Pure f <*> m = fmap f m
  Join f <*> m = Join (fmap (<*> m) f)

instance Functor f => Monad (Free f) where
  Pure a >>= f = f a
  Join m >>= f = Join (fmap (>>= f) m)

-----------------------------------------------------------------------------
-- Church Free

newtype F f a = F {runF :: forall r. (f r -> r) -> (a -> r) -> r}
  deriving (Functor)

instance Applicative (F f) where
  pure a = F $ \_ k -> k a
  F mf <*> F mx = F $ \alg k -> mf alg (\g -> mx alg (k . g))

instance Monad (F f) where
  m >>= f = F $ \alg k -> runF m alg (\a -> runF (f a) alg k)

toFree :: F f a -> Free f a
toFree (F f) = f Join Pure

foldF :: Monad m => (forall x. f x -> m x) -> F f a -> m a
foldF alg (F f) = f (\fx -> alg fx >>= id) pure

newtype Eff f a = Eff {runEff :: forall m. Monad m => (forall x. f x -> m x) -> m a}
  deriving (Functor)

instance Applicative (Eff f) where
  pure a = Eff $ \_ -> pure a
  Eff mf <*> Eff mx = Eff $ \alg -> mf alg <*> mx alg

instance Monad (Eff f) where
  m >>= f = Eff $ \alg -> runEff m alg >>= (\a -> runEff (f a) alg)

-----------------------------------------------------------------------------
-- https://apfelmus.nfshost.com/articles/operational-monad.html

data Program stmt a where
  Return :: a -> Program stmt a
  Then :: stmt a -> (a -> Program stmt b) -> Program stmt b

deriving instance Functor (Program stmt)

instance Applicative (Program stmt) where
  pure = Return
  Return f <*> r      = fmap f r
  (s `Then` fs) <*> r = s `Then` (\a -> fs a <*> r)

instance Monad (Program stmt) where
  (Return a) >>= xs    = xs a
  (s `Then` xs) >>= ys = s `Then` (\a -> xs a >>= ys)

data State s a where
  Get :: State s s
  Put :: s -> State s ()

runState :: s -> Program (State s) a -> (s, a)
runState s (Return x)       = (s, x)
runState s (Get `Then` k)   = runState s (k s)
runState _ (Put s `Then` k) = runState s (k ())

-----------------------------------------------------------------------------
-- http://okmij.org/ftp/Haskell/Reflection.html
data FTCQueue m a b where
    Leaf :: (a -> m b) -> FTCQueue m a b
    Node :: FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b

instance (Applicative f) => Category (FTCQueue f) where
    id = Leaf pure
    (.) = flip Node

-- | Append an operation to the right of the tree. [O(1)]
(|>) :: FTCQueue m a x -> (x -> m b) -> FTCQueue m a b
t |> r = Node t (Leaf r)
{-# INLINE (|>) #-}

-- | Left view deconstruction data structure.
data ViewL m a b where
    TOne :: (a -> m b) -> ViewL m a b
    (:|) :: (a -> m x) -> FTCQueue m x b -> ViewL m a b

-- | Append two trees of operations. [O(1)]
(><) :: FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b
t1 >< t2 = Node t1 t2
{-# INLINE (><) #-}

-- | Left view deconstruction. [average O(1)]
tviewl :: FTCQueue m a b -> ViewL m a b
tviewl (Leaf r) = TOne r
tviewl (Node t1 t2) = go t1 t2
  where
    go :: FTCQueue m a x -> FTCQueue m x b -> ViewL m a b
    go (Leaf r) tr       = r :| tr
    go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)

data Freer f a
    = -- | A pure value.
      Val a
    | -- | An effectful operation.
      forall x. Op (f x) (FTCQueue (Freer f) x a)
                      -- ^ the continuation of the operation.

instance Functor (Freer f) where
    fmap f = \case
        Val x -> Val (f x)
        Op u q -> Op u (q |> (Val . f))
    {-# INLINE fmap #-}

instance Applicative (Freer f) where
    pure = Val
    {-# INLINE pure #-}

    Val f <*> Val x  = Val $ f x
    Val f <*> Op u q = Op u (q |> (Val . f))
    Op u q <*> m     = Op u (q |> (<$> m))
    {-# INLINE (<*>) #-}

instance Monad (Freer f) where
    m >>= k = case m of
        Val x  -> k x
        Op e q -> Op e (q |> k)
    {-# INLINE (>>=) #-}

-----------------------------------------------------------------------------
-- https://blog.poisson.chat/posts/2019-10-26-reasonable-continuations.html

newtype Cont r a = Cont {(>>-) :: (a -> r) -> r}
  deriving (Functor)

instance Applicative (Cont r) where
  pure a = Cont ($ a)
  Cont mf <*> Cont mx = Cont $ \k -> mf (\g -> mx (k . g))

instance Monad (Cont r) where
  m >>= f = Cont $ \k -> m >>- (\a -> f a >>- k)

runCont :: Cont r r -> r
runCont m = m >>- id

reset :: Cont a a -> Cont r a
reset = pure . runCont

shift :: ((a -> r) -> Cont r r) -> Cont r a
shift f = Cont (runCont . f)

type Pure a = forall r. Cont r a

runPure :: Pure a -> a
runPure (Cont m) = m id

type Except e a = forall r. Cont (Either e r) a

runExcept :: Except e a -> Either e a
runExcept (Cont m) = m Right

throw :: e -> Except e a
throw e = Cont (\_ -> Left e)

type State' s a = forall r. Cont (s -> r) a

runState' :: Cont (s -> (a, s)) a -> s -> (a, s)
runState' (Cont m) = m (,)

get :: Cont (s -> s) s
get = Cont (\k s -> k s s)

put :: s -> Cont (s -> s) ()
put s = Cont (\k _ -> k () s)

type ContT r m a = Cont (m r) a

lift :: Monad m => m a -> ContT r m a
lift m = Cont (m >>=)

type Codensity m a = forall r. Cont (m r) a

lowerCodensity :: Applicative m => Codensity m a -> m a
lowerCodensity m = m >>- pure

improve :: Functor f => Codensity (Free f) a -> Free f a
improve = lowerCodensity
