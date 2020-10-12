{-# LANGUAGE DeriveFunctor #-}

module Formula where

import Control.Monad.State
data Term a
  = Var a
  | Zero
  | One
  | Add (Term a) (Term a)
  deriving (Functor, Show)

data Formula a
  = Top
  | Equals (Term a) (Term a) -- The atomic formulae
  | And (Formula a) (Formula a)
  | Or (Formula a) (Formula a)
  | Not (Formula a)
  | Forall a (Formula a)
  | Exists a (Formula a)
  deriving (Show)

preprocess :: Formula String -> Formula Int
preprocess = prenex . normalise . standardise

-- Create a unique number of variables in a sentance, i.e. a formula with no free variables
standardise :: Formula String -> Formula Int
standardise = go []
  where
    -- Register a new variable
    insert :: String -> [(String, Int)] -> (Int, [(String, Int)])
    insert x [] = (0, [(x, 0)])
    insert x m =
      let y = maximum [z | (_, z) <- m] + 1
       in (y, (x, y) : m)

    -- Rename the variables in a term
    rename :: [(String, Int)] -> Term String -> Term Int
    rename m =
      fmap
        ( \a ->
            case lookup a m of
              Nothing -> error "Variable not in scope!"
              Just b -> b
        )

    go :: [(String, Int)] -> Formula String -> Formula Int
    go _ Top = Top
    go m (Equals x y) = Equals (rename m x) (rename m y)
    go m (And p q) = And (go m p) (go m q)
    go m (Or p q) = Or (go m p) (go m q)
    go m (Not p) = Not (go m p)
    go m (Forall x p) =
      let (y, m') = insert x m
       in Forall y (go m' p)
    go m (Exists x p) =
      let (y, m') = insert x m
       in Exists y (go m' p)

fresh :: State Int Int
fresh = do
  x <- get
  put (x + 1)
  return x

-- Turn a term into a formula and a variable which has the same value
termToVar :: Term Int -> State Int (Formula Int, Int)
termToVar t = do
  x <- get
  (p, y) <- go t
  x' <- get
  return (foldr Exists p [x .. (x' - 1)], y)
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
normalise :: Formula Int -> Formula Int
normalise p = evalState (go p) 0
  where
    go :: Formula Int -> State Int (Formula Int)
    go Top = return Top
    go (Equals t1 t2) = do
      z <- fresh
      (p, x) <- termToVar t1
      (q, y) <- termToVar t2
      return $ Exists z $ And p $ And q $ And (Equals (Var z) Zero) (Equals (Add (Var x) (Var z)) (Var y))
    go (And p q) = do
      p' <- go p
      q' <- go q
      return (And p' q')
    go (Or p q) = do
      p' <- go p
      q' <- go q
      return (Or p' q')
    go (Not p) = Not <$> go p
    go (Forall x p) = do
      y <- get
      put (max (x + 1) y)
      Forall x <$> go p
    go (Exists x p) = do
      y <- get
      put (max (x + 1) y)
      Exists x <$> go p

-- Convert a standardised formula to prenex normal form
prenex :: Formula a -> Formula a
prenex Top = Top
prenex (Equals x y) = Equals x y
prenex (And p q) =
  -- TODO: Ordering when both p and q are quantifiers
  case (prenex p, prenex q) of
    (Forall x p', q') -> Forall x (prenex (And p' q'))
    (Exists x p', q') -> Exists x (prenex (And p' q'))
    (p', Forall x q') -> Forall x (prenex (And p' q'))
    (p', Exists x q') -> Exists x (prenex (And p' q'))
    (p', q') -> And p' q'
prenex (Or p q) =
  -- TODO: Ordering when both p and q are quantifiers
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