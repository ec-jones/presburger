{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}

module Formula where

data Term a
  = Var a
  | Zero
  | One
  | Add (Term a) (Term a)
  deriving (Eq, Functor, Foldable)

data Formula a
  = Equals (Term a) (Term a) -- The atomic formulae
  | Top
  | And (Formula a) (Formula a)
  | Or (Formula a) (Formula a)
  | Not (Formula a)
  | Forall a (Formula a)
  | Exists a (Formula a)
  deriving (Eq, Functor, Foldable)

-- Turn a term into a formula and a variable which has the same value
-- x is the next fresh variables
termToVar :: Term Int -> Int -> (Int, Formula Int, Int)
termToVar (Var x) y = (y, Top, x)
termToVar Zero x = (x + 1, Exists x (Equals (Var x) Zero), x)
termToVar One x = (x + 1, Exists x (Equals (Var x) One), x)
termToVar (Add t1 t2) x =
  let (x', p, y) = termToVar t1 (x + 1)
      (x'', q, z) = termToVar t2 x'
   in (x'', Exists x (And p (And q (Equals (Add (Var y) (Var z)) (Var x)))), z)

-- Convert all atoms to one of the forms: x + y = z, x = 0, or y = 1
normalise :: Formula Int -> Int -> (Int, Formula Int)
normalise Top x = (x, Top)
normalise (Equals t1 t2) x =
  let (x', p, y) = termToVar t1 (x + 1)
      (x'', q, z) = termToVar t2 x'
   in (x'', Exists x (And p (And q (And (Equals (Var x) Zero) (Equals (Add (Var y) (Var z)) (Var z))))))
normalise (And p q) x =
  let (x', p') = normalise p x
      (x'', q') = normalise q x'
   in (x'', And p' q')
normalise (Or p q) x =
  let (x', p') = normalise p x
      (x'', q') = normalise q x'
   in (x'', Or p' q')
normalise (Not p) x = fmap Not (normalise p x)
normalise (Forall x p) y = fmap (Forall x) (normalise p y)
normalise (Exists x p) y = fmap (Exists x) (normalise p y)

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

preprocess :: Formula String -> Formula Int
preprocess p =
  let p' = prenex (standardise p)
   in snd (normalise p' (maximum p'))