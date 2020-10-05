module Automata where

import Data.List (subsequences, (\\))

-- A (non-)deterministic finite automata over bit vectors
data Automaton q = Automaton
  { states :: [q],
    dim :: Int,
    delta :: q -> [([Bool], q)],
    start :: q,
    final :: [q]
  }

-- x + y = z
equation :: Automaton Bool
equation =
  Automaton
    { states = [False, True], -- carry?
      dim = 3,
      delta = \q ->
        if q
          then
            [ ([False, False, False], False),
              ([False, True, True], False),
              ([True, False, True], False),
              ([True, True, False], False)
            ]
          else
            [ ([False, False, True], False),
              ([False, True, False], True),
              ([True, False, False], True),
              ([True, True, True], True)
            ],
      start = False,
      final = [False]
    }

-- Check if every transition is unique
isDeterministic :: Eq q => Automaton q -> Bool
isDeterministic a = all (isFunc . delta a) (states a)
  where
    isFunc [] = True
    isFunc ((x, y) : xys) =
      case lookup x xys of
        Nothing -> isFunc xys
        Just z -> y == z && isFunc xys

-- The powet set construction
determinise :: Eq q => Automaton q -> Automaton [q]
determinise a =
  Automaton
    { states = subsequences (states a),
      dim = dim a,
      delta = \qs ->
        [ (n, [q' | (m, q') <- delta a q, m == n])
          | q <- qs,
            (n, _) <- delta a q
        ],
      start = [start a],
      final =
        [ qs
          | qs <- subsequences (states a),
            any (`elem` final a) qs
        ]
    }

-- Check if the automaton accept any string
empty :: Eq q => Automaton q -> Bool
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

intersection :: Automaton a -> Automaton b -> Automaton (a, b)
intersection a b
  | dim a /= dim b = error "The automata's dimensions do not match!"
intersection a b =
  Automaton
    { states =
        [ (qa, qb)
          | qa <- states a,
            qb <- states b
        ],
      dim = dim a,
      delta = \(qa, qb) ->
        [ (n, (qa', qb'))
          | (n, qa') <- delta a qa,
            (m, qb') <- delta b qb,
            n == m
        ],
      start = (start a, start b),
      final =
        [ (qa, qb)
          | qa <- final a,
            qb <- final b
        ]
    }

union :: Automaton a -> Automaton b -> Automaton (a, b)
union a b =
  (intersection a b)
    { final =
        [ (qa, qb)
          | qa <- final a,
            qb <- states b
        ]
          ++ [ (qa, qb)
               | qa <- states a,
                 qb <- final b
             ]
    }

complement :: Eq a => Automaton a -> Automaton [a]
complement a =
  let a' = determinise a
   in a'
        { final = states a' \\ final a'
        }

-- Eliminate the top row of all vectors
project :: Automaton q -> Automaton q
project a | dim a == 0 = error "Cannot project from an empty vector"
project a =
  Automaton
    { states = states a,
      dim = dim a - 1,
      delta = \q -> [(tail n, q') | (n, q') <- delta a q],
      start = start a,
      final = final a
    }
