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
  | And (Formula a) (Formula a)
  | Or (Formula a) (Formula a)
  | Not (Formula a)
  | Forall a (Formula a)
  | Exists a (Formula a)
  deriving (Eq, Functor)

-- -- Convert addition term into a variable with a supply of fresh variables
-- add :: Term a -> Term a -> [a] -> (Maybe (Formula a), a)
-- add (Var x) (Var y) = (Just (Exists z (Equals (Add (Var x) (Var y)) z)), z)
-- add (Var x) Zero = (Nothing, x)
-- add (Var x) One = (Just (Exists z (Exists y (And (Equals (Add (Var x) (Var y)) z) (Equals y One)))), z)
-- add (Var x) (Add y z) =
--   let (p, w) = add y z
--   in (Just (Exists v (And (Equals (Add (Var x) (Var w)) v) p)), v)

-- -- Smart constructor for equality
-- equals :: Term a -> Term a -> Formula a
-- equals z Zero = Equals z Zero
-- equals z One = Equals z One
-- equals z (Add (Var x) (Var y)) = Equals (Add (Var x) (Var y)) z
-- equals z (Add Zero y) = Equals z y
-- equals z (Add x Zero) = Equals z x
-- equals z (Add x y) = _

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