{-# LANGUAGE DeriveFunctor #-}

module Formula where

import Control.Monad.State (MonadState (get, put), State, evalState)

data Term a
  = Var a
  | Zero
  | One
  | Add (Term a) (Term a)
  deriving (Functor)

data Formula a
  = Equals (Term a) (Term a) -- The atomic formulae
  | Top
  | And (Formula a) (Formula a)
  | Or (Formula a) (Formula a)
  | Not (Formula a)
  | Forall a (Formula a)
  | Exists a (Formula a)

preprocess :: Formula String -> Formula Int
preprocess p =
  evalState
    ( prenex <$> (standardise p >>= normalise)
    )
    ([], 0)

-- Allows us to keep track of variables names, and create fresh ones
type Scope = State ([(String, Int)], Int)

fresh :: Scope Int
fresh = do
  (m, x) <- get
  put (m, x + 1)
  return x

-- Record all fresh variables that a function produces
listen :: Scope a -> Scope (a, [Int])
listen ma = do
  (_, x) <- get
  a <- ma
  (_, x') <- get
  return (a, [x .. (x' - 1)])

-- Record the standardisation of a variable
addToScope :: String -> Int -> Scope ()
addToScope x x' = do
  (m, y) <- get
  put ((x, x') : m, max y x')

-- Rename the variables in a term
rename :: Term String -> Scope (Term Int)
rename t = do
  (m, _) <- get
  return
    ( fmap
        ( \a ->
            case lookup a m of
              Nothing -> error "Variable not in scope!"
              Just b -> b
        )
        t
    )

-- Create a unique number of variables in a sentance, i.e. a formula with no free variables
standardise :: Formula String -> Scope (Formula Int)
standardise Top = return Top
standardise (Equals x y) = do
  x' <- rename x
  y' <- rename y
  return (Equals x' y')
standardise (And p q) = do
  p' <- standardise p
  q' <- standardise q
  return (And p' q')
standardise (Or p q) = do
  p' <- standardise p
  q' <- standardise q
  return (Or p' q')
standardise (Not p) = do
  p' <- standardise p
  return (Not p')
standardise (Forall x p) = do
  x' <- fresh
  addToScope x x'
  p' <- standardise p
  return (Forall x' p')
standardise (Exists x p) = do
  x' <- fresh
  addToScope x x'
  p' <- standardise p
  return (Exists x' p')

-- Turn a term into a formula and a variable which has the same value
termToVar :: Term Int -> Scope (Formula Int, Int)
termToVar t = do
  ((p, y), xs) <- listen (go t)
  return (foldr Exists p xs, y)
  where
    go (Var x) = return (Top, x)
    go Zero = do
      x <- fresh
      return (Equals (Var x) Zero, x)
    go One = do
      x <- fresh
      return (Equals (Var x) One, x)
    go (Add t1 t2) = do
      (p, x) <- go t1
      (q, y) <- go t2
      z <- fresh
      return (And p (And q (Equals (Add (Var x) (Var y)) (Var z))), z)

-- Convert all atoms to one of the forms: x + y = z, x = 0, or y = 1
normalise :: Formula Int -> Scope (Formula Int)
normalise Top = return Top
normalise (Equals t1 t2) = do
  (p, x) <- termToVar t1
  (q, y) <- termToVar t2
  z <- fresh
  return (Exists z (And p (And q (And (Equals (Var x) Zero) (Equals (Add (Var y) (Var z)) (Var z))))))
normalise (And p q) = do
  p' <- normalise p
  q' <- normalise q
  return (And p' q')
normalise (Or p q) = do
  p' <- normalise p
  q' <- normalise q
  return (Or p' q')
normalise (Not p) = fmap Not (normalise p)
normalise (Forall x p) = fmap (Forall x) (normalise p)
normalise (Exists x p) = fmap (Exists x) (normalise p)

-- Convert a standardised formula to prenex normal form
prenex :: Formula a -> Formula a
prenex Top = Top
prenex (Equals x y) = Equals x y
prenex (And p q) =
  case (prenex p, prenex q) of
    (Forall x p', q') -> Forall x (prenex (And p' q'))
    (Exists x p', q') -> Exists x (prenex (And p' q'))
    (p', Forall x q') -> Forall x (prenex (And p' q'))
    (p', Exists x q') -> Exists x (prenex (And p' q'))
    (p', q') -> And p' q'
prenex (Or p q) =
  case (prenex p, prenex q) of
    (Forall x p', q') -> Forall x (prenex (Or p' q'))
    (Exists x p', q') -> Exists x (prenex (Or p' q'))
    (p', Forall x q') -> Forall x (prenex (Or p' q'))
    (p', Exists x q') -> Exists x (prenex (Or p' q'))
    (p', q') -> Or p' q'
prenex (Not p) =
  case prenex p of
    Forall x p' -> Exists x (prenex (Not p'))
    Exists x p' -> Forall x (prenex (Not p'))
    p' -> Not p'
prenex (Forall x p) = Forall x (prenex p)
prenex (Exists x p) = Exists x (prenex p)