module Automaton where

import Control.Monad.State
import Data.List

-- The type of states
data Q
  = Off
  | On
  | Pair Q Q
  | Set [Q]
  deriving (Eq, Show)

-- The type of alphabet symbols
type Sigma = [Bool]

-- The type of transition functions
type Delta = Q -> Sigma -> [Q]

-- A (non-)deterministic finite automata over bit vectors
data Automaton = Automaton
  { states :: [Q],
    dim :: Int,
    delta :: Delta,
    start :: Q,
    final :: Q -> Bool
  }

-- The automaton's alphabet
sigma :: Automaton -> [Sigma]
sigma a = replicateM (dim a) [False, True]

-- The set of states which follow from a states q
succs :: Automaton -> Q -> [Q]
succs a q = sigma a >>= delta a q

-- Check if an automaton accepts a particular string
accepts :: Automaton -> [Sigma] -> Bool
accepts a = go (start a)
  where
    go :: Q -> [Sigma] -> Bool
    go q [] = final a q
    go q (x : xs) =
      any (`go` xs) (delta a q x)

-- Check if every traxsition is unique
isDeterministic :: Automaton -> Bool
isDeterministic a = all (isFunc . delta a) (states a)
  where
    isFunc :: (Sigma -> [Q]) -> Bool
    isFunc f = all (isSingleton . f) (sigma a)

    isSingleton :: [Q] -> Bool
    isSingleton = (== 1) . length

-- Check if the automaton accept any string
isEmpty :: Automaton -> Bool
isEmpty a = not $ evalState (search (start a)) []
  where
    -- Depth-first search for to final state
    search :: Q -> State [Q] Bool
    search q
      | final a q = return True
      | otherwise = do
        qs <- get -- The set of previously visited states
        if q `elem` qs
          then return False -- q has already been visited
          else do
            modify (q :) -- Mark q as visited
            foldr
              ( \q' k -> do
                  found <- search q'
                  if found
                    then return True -- Exit if a final state has been reached
                    else k
              )
              (return False)
              (succs a q) -- Search every successor of q

-- The power set construction
determinise :: Automaton -> Automaton
determinise a | isDeterministic a = a
determinise a =
  a
    { states = Set <$> subsequences (states a),
      delta = \q xs ->
        case q of
          Set qs -> [Set (nub (qs >>= \q' -> delta a q' xs))]
          _ -> [],
      start = Set [start a],
      final = \q ->
        case q of
          Set qs -> any (final a) qs
          _ -> False
    }

-- Update the set of states reachable
trim :: Automaton -> Automaton
trim a =
  let qs = go [start a]
   in a {states = qs}
  where
    go qs =
      let new = nub [q' | q <- qs, xs <- sigma a, q' <- delta a q xs, q' `notElem` qs]
       in if null new
            then qs
            else go (new ++ qs)

-----------------------------------------------------------------
-------------------------- Combinators --------------------------
-----------------------------------------------------------------

-- The trivial automaton
empty :: Automaton
empty =
  Automaton
    { states = [Off],
      dim = 0,
      delta = \_ _ -> [Off],
      start = Off,
      final = \q ->
        case q of
          Off -> True
          _ -> False
    }

-- An automaton with x set to zero or one
zero, one :: Int -> Automaton
zero x =
  Automaton
    { states = [Off],
      dim = x + 1,
      delta = \q xs ->
        case q of
          Off
            | xs !! x -> []
            | otherwise -> [Off]
          _ -> [],
      start = Off,
      final = \q ->
        case q of
          Off -> True
          _ -> False
    }
one x =
  Automaton
    { states = [Off, On], -- first digit?
      dim = x + 1,
      delta = \q xs ->
        case q of
          Off
            | xs !! x -> []
            | otherwise -> [Off]
          On
            | xs !! x -> [Off]
            | otherwise -> []
          _ -> [],
      start = On,
      final = \q ->
        case q of
          Off -> True
          _ -> False
    }

-- x + y = z
equation :: Int -> Int -> Int -> Automaton
equation x y z =
  Automaton
    { states = [Off, On], -- to carry or not
      dim = maximum [x, y, z] + 1,
      delta = \q xs ->
        case q of
          Off
            | xs !! z == (xs !! x /= xs !! y) -> [fromBool (xs !! x && xs !! y)]
            | otherwise -> []
          On
            | xs !! z == (xs !! x == xs !! y) -> [fromBool (xs !! x || xs !! y)]
            | otherwise -> []
          _ -> [],
      start = Off,
      final = \q ->
        case q of
          Off -> True
          _ -> False
    }
  where
    fromBool :: Bool -> Q
    fromBool False = Off
    fromBool True = On

-- Eliminate dth variables from automaton
project :: Int -> Automaton -> Automaton
project d a | dim a /= d + 1 = error "Cannot eliminate variables out of order!"
project _ a =
  a
    { dim = dim a - 1,
      delta = \q xs -> extend xs >>= delta a q
    }
  where
    -- The inverse of take
    extend xs = [xs ++ [p] | p <- [False, True]]

-- Extend an automaton to d bits
antiproject :: Int -> Automaton -> Automaton
antiproject d a | dim a >= d = a
antiproject d a =
  a
    { dim = d,
      delta = \q -> delta a q . take (dim a)
    }

-- Intersection of two languages
intersection :: Automaton -> Automaton -> Automaton
intersection a b =
  let a' = antiproject (dim b) a
      b' = antiproject (dim a) b
   in Automaton
        { states = Pair <$> states a' <*> states b',
          dim = dim a',
          delta = \q xs ->
            case q of
              Pair qa qb -> Pair <$> delta a' qa xs <*> delta b' qb xs
              _ -> [],
          start = Pair (start a') (start b'),
          final = \q ->
            case q of
              Pair qa qb -> final a qa && final a qb
              _ -> False
        }

-- Union of two languages
union :: Automaton -> Automaton -> Automaton
union a b =
  let a' = antiproject (dim b) a
      b' = antiproject (dim a) b
   in Automaton
        { states = Pair <$> states a' <*> states b',
          dim = dim a',
          delta = \q xs ->
            case q of
              Pair qa qb -> Pair <$> delta a' qa xs <*> delta b' qb xs
              _ -> [],
          start = Pair (start a') (start b'),
          final = \q ->
            case q of
              Pair qa qb -> final a qa || final a qb
              _ -> False
        }

-- The automaton which accepts every string NOT found in the original
complement :: Automaton -> Automaton
complement a =
  let a' = determinise a
   in a'
        { final = not . final a'
        }