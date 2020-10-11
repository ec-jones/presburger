module Automaton where

import Control.Monad (replicateM)
import Data.List (subsequences, (\\))

data State
  = On
  | Off
  | Pair State State
  | Set [State]
  deriving (Eq)

-- A (non-)deterministic finite automata over bit vectors
data Automaton = Automaton
  { states :: [State],
    dim :: Int,
    delta :: State -> [([Bool], State)],
    start :: State,
    final :: [State]
  }

-- x + y = z
equation :: Automaton
equation =
  Automaton
    { states = [Off, On], -- to carry or not
      dim = 3,
      delta = \q ->
        case q of
          Off ->
            [ ([False, False, True], Off),
              ([False, True, False], On),
              ([True, False, False], On),
              ([True, True, True], On)
            ]
          On ->
            [ ([False, False, False], Off),
              ([False, True, True], Off),
              ([True, False, True], Off),
              ([True, True, False], Off)
            ]
          _ -> [],
      start = Off,
      final = [Off]
    }

-- An automaton with n set to zero or one
zero :: Int -> Automaton
zero n =
  Automaton
    { states = [Off],
      dim = n,
      delta = const [(False : ns, Off) | ns <- replicateM (n - 1) [False, True]],
      start = Off,
      final = [Off]
    }

one :: Int -> Automaton
one n =
  Automaton
    { states = [Off, On], -- first digit
      dim = n,
      delta = \i ->
        case i of
          On -> [(True : ns, On) | ns <- replicateM (n - 1) [False, True]]
          Off -> [(False : ns, On) | ns <- replicateM (n - 1) [False, True]]
          _ -> [],
      start = Off,
      final = [Off, On]
    }

-- Check if every transition is unique
isDeterministic :: Automaton -> Bool
isDeterministic a = all (isFunc . delta a) (states a)
  where
    isFunc [] = True
    isFunc ((x, y) : xys) =
      case lookup x xys of
        Nothing -> isFunc xys
        Just z -> y == z && isFunc xys

-- The powet set construction
determinise :: Automaton -> Automaton
determinise a =
  Automaton
    { states = fmap Set (subsequences (states a)),
      dim = dim a,
      delta = \qs ->
        case qs of
          Set qs' ->
            [ (n, Set [q' | (m, q') <- delta a q, m == n])
              | q <- qs',
                (n, _) <- delta a q
            ]
          _ -> [],
      start = Set [start a],
      final =
        [ Set qs
          | qs <- subsequences (states a),
            any (`elem` final a) qs
        ]
    }

-- Check if the automaton accept any string
empty :: Automaton -> Bool
empty a = snd $ search (start a) []
  where
    -- Depth-first search for to final state
    search q qs
      | q `elem` final a = (qs, True)
      | q `elem` qs = (qs, False) -- q has already been visited
      | otherwise =
        foldr
          ( \(_, q') (qs', found) ->
              if found
                then (qs', True)
                else search q' qs'
          )
          (q : qs, False)
          (delta a q)

intersection :: Automaton -> Automaton -> Automaton
intersection a b
  | dim a /= dim b = error "The automata's dimensions do not match!"
intersection a b =
  Automaton
    { states =
        [ Pair qa qb
          | qa <- states a,
            qb <- states b
        ],
      dim = dim a,
      delta = \q ->
        case q of
          Pair qa qb ->
            [ (n, Pair qa' qb')
              | (n, qa') <- delta a qa,
                (m, qb') <- delta b qb,
                n == m
            ]
          _ -> [],
      start = Pair (start a) (start b),
      final =
        [ Pair qa qb
          | qa <- final a,
            qb <- final b
        ]
    }

union :: Automaton -> Automaton -> Automaton
union a b =
  (intersection a b)
    { final =
        [ Pair qa qb
          | qa <- final a,
            qb <- states b
        ]
          ++ [ Pair qa qb
               | qa <- states a,
                 qb <- final b
             ]
    }

complement :: Automaton -> Automaton
complement a =
  let a' = determinise a
   in a'
        { final = states a' \\ final a'
        }

-- Eliminate the top row of all vectors
project :: Automaton -> Automaton
project a | dim a == 0 = error "Cannot eliminate variables out of order"
project a =
  Automaton
    { states = states a,
      dim = dim a - 1,
      delta = \q -> [(tail n, q') | (n, q') <- delta a q],
      start = start a,
      final = final a
    }

-- Extend an automaton to n bits
antiproject :: Int -> Automaton -> Automaton
antiproject n a =
  Automaton
    { states = states a,
      dim = max (dim a) n,
      delta = \q -> [(m, q') | (n, q') <- delta a q, m <- extend n],
      start = start a,
      final = final a
    }
  where
    extend :: [Bool] -> [[Bool]]
    extend xs
      | length xs >= n = [xs]
      | otherwise = [e ++ xs | e <- replicateM (length xs - n) [False, True]]