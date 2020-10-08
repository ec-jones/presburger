{-# LANGUAGE DeriveFunctor #-}

module Formula where

data Term a
  = Var a
  | Zero
  | One
  | Add (Term a) (Term a)
  deriving (Eq, Functor)

data Formula a
  = Equals (Term a) (Term a) -- The atomic formulae
  | Top
  | And (Formula a) (Formula a)
  | Or (Formula a) (Formula a)
  | Not (Formula a)
  | Forall a (Formula a)
  | Exists a (Formula a)
  deriving (Eq, Functor)

-- Turn a term into a formula and a variable which has the same value
-- xs is a list of fresh variables
termToVar :: Term a -> [a] -> ([a], Formula a, a)
termToVar (Var x) xs = (xs, Top, x)
termToVar Zero (x : xs) = (xs, Exists x (Equals (Var x) Zero), x)
termToVar One (x : xs) = (xs, Exists x (Equals (Var x) One), x)
termToVar (Add t1 t2) (z : xs) =
  let (xs', fy, x) = termToVar t1 xs
      (xs'', fx, y) = termToVar t2 xs'
   in (xs'', Exists z (And fx (And fy (Equals (Add (Var x) (Var y)) (Var z)))), z)
termToVar _ _ = error "Insufficient fresh variables!"

-- Convert all atoms to one of the forms: x + y = z, x = 0, or y = 1
normalise :: Formula a -> [a] -> ([a], Formula a)
normalise Top xs = (xs, Top)
normalise (Equals t1 t2) (z : xs) =
  let (xs', p, x) = termToVar t1 xs
      (xs'', q, y) = termToVar t2 xs'
   in (xs'', Exists z (And (Equals (Add (Var x) (Var y)) (Var z)) (And p q)))
normalise (And p q) xs =
  let (xs', p') = normalise p xs
      (xs'', q') = normalise q xs'
   in (xs'', And p' q')
normalise (Or p q) xs =
  let (xs', p') = normalise p xs
      (xs'', q') = normalise q xs'
   in (xs'', Or p' q')
normalise (Not p) xs = Not <$> normalise p xs
normalise (Forall x p) xs = Forall x <$> normalise p xs
normalise (Exists x p) xs = Exists x <$> normalise p xs
normalise _ _ = error "Insufficient fresh variables!"

-- Rename the variables in a term
rename :: (Eq a, Functor f) => [(a, b)] -> f a -> f b
rename m =
  fmap
    ( \a ->
        case lookup a m of
          Nothing -> error "Variable not in scope!"
          Just b -> b
    )

-- Create a unique number of variables in a sentance, i.e. a formula with no free variables
standardise :: Formula String -> Formula Int
standardise = snd . go []
  where
    go :: [(String, Int)] -> Formula String -> ([(String, Int)], Formula Int)
    go m Top = (m, Top)
    go m (Equals x y) = (m, Equals (rename m x) (rename m y))
    go m (And p q) =
      let (m', p') = go m p
          (m'', q') = go m' q
       in (m'', And p' q')
    go m (Or p q) =
      let (m', p') = go m p
          (m'', q') = go m' q
       in (m'', Or p' q')
    go m (Not p) =
      let (m', p') = go m p
       in (m', Not p')
    go m (Forall x p) =
      let fresh = maximum (map snd m) + 1
          m' = (x, fresh) : m
          (m'', p') = go m' p
       in (m'', Forall fresh p')
    go m (Exists x p) =
      let fresh = maximum (map snd m) + 1
          m' = (x, fresh) : m
          (m'', p') = go m' p
       in (m'', Exists fresh p')

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