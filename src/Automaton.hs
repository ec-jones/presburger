module Automaton where

import Control.Monad (replicateM)
import Data.List (subsequences, (\\))

data State
  = On
  | Off
  | Pair State State
  | Set [State]
  deriving (Eq)

fromBool :: Bool -> State
fromBool False = Off
fromBool True = On

-- A (non-)deterministic finite automata over bit vectors
data Automaton = Automaton
  { states :: [State],
    dim :: Int,
    delta :: State -> [Bool] -> [State],
    start :: State,
    final :: [State]
  }

-- x + y = z
equation :: Int -> Int -> Int -> Automaton
equation x y z =
  Automaton
    { states = [Off, On], -- to carry or not
      dim = maximum [x + 1, y + 1, z + 1],
      delta = \q ns ->
        case q of
          Off
            | ns !! z == (ns !! x == ns !! y) -> [fromBool (ns !! x || ns !! y)]
            | otherwise -> []
          On
            | ns !! z == (ns !! x /= ns !! y) -> [fromBool (ns !! x && ns !! y)]
            | otherwise -> []
          _ -> [],
      start = Off,
      final = [Off]
    }

-- An automaton with n set to zero or one
zero :: Int -> Automaton
zero x =
  Automaton
    { states = [Off],
      dim = x + 1,
      delta = \q ns ->
        case q of
          Off
            | ns !! x -> [Off]
            | otherwise -> []
          _ -> [],
      start = Off,
      final = [Off]
    }

one :: Int -> Automaton
one x =
  Automaton
    { states = [Off, On], -- first digit
      dim = x + 1,
      delta = \q ns ->
        case q of
          On
            | ns !! x -> [Off]
            | otherwise -> []
          Off
            | ns !! x -> []
            | otherwise -> [Off]
          _ -> [],
      start = On,
      final = [Off, On]
    }

-- Check if every transition is unique
isDeterministic :: Automaton -> Bool
isDeterministic a = all (isFunc . delta a) (states a)
  where
    isFunc :: ([Bool] -> [State]) -> Bool
    isFunc f = all (\ns -> length (f ns) == 1) (replicateM (dim a) [False, True])

-- The powet set construction
determinise :: Automaton -> Automaton
determinise a =
  Automaton
    { states = fmap Set (subsequences (states a)),
      dim = dim a,
      delta = \q ns ->
        case q of
          Set qs ->
            [Set (qs >>= \q' -> delta a q' ns)]
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
          ( \q' (qs', found) ->
              if found
                then (qs', True)
                else search q' qs'
          )
          (q : qs, False)
          (replicateM (dim a) [False, True] >>= delta a q)

intersection :: Automaton -> Automaton -> Automaton
intersection a b =
  let a' = antiproject (dim a) a
      b' = antiproject (dim b) b
   in Automaton
        { states =
            [ Pair qa qb
              | qa <- states a',
                qb <- states b'
            ],
          dim = dim a',
          delta = \q ns ->
            case q of
              Pair qa qb ->
                [Pair qa' qb' | qa' <- delta a' qa ns, qb' <- delta b' qb ns]
              _ -> [],
          start = Pair (start a') (start b'),
          final =
            [ Pair qa qb
              | qa <- final a',
                qb <- final b'
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
      delta = \q ns -> [ns ++ [False], ns ++ [True]] >>= delta a q,
      start = start a,
      final = final a
    }

-- Extend an automaton to n bits
antiproject :: Int -> Automaton -> Automaton
antiproject n a =
  Automaton
    { states = states a,
      dim = max (dim a) n,
      delta = \q ns -> delta a q (take (dim a) ns),
      start = start a,
      final = final a
    }