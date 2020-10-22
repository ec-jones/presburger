module Presburger where

import Automaton
import Formula
import Parser

-- Construct an automaton for a standardised formula
formulaToAutomaton :: Formula Int -> Automaton
formulaToAutomaton Top = empty
formulaToAutomaton (Equals (Var x) Zero) = zero x
formulaToAutomaton (Equals (Var x) One) = one x
formulaToAutomaton (Equals (Add (Var x) (Var y)) (Var z)) = equation x y z
formulaToAutomaton (And p q) = intersection (formulaToAutomaton p) (formulaToAutomaton q)
formulaToAutomaton (Or p q) = union (formulaToAutomaton p) (formulaToAutomaton q)
formulaToAutomaton (Not p) = complement (formulaToAutomaton p)
formulaToAutomaton (Exists x p) = project x (formulaToAutomaton p)
formulaToAutomaton (Forall x p) = complement (project x (complement (formulaToAutomaton p)))
formulaToAutomaton _ = error "Formula is not in atomic form!"

stringToAutomaton :: String -> Automaton
stringToAutomaton = formulaToAutomaton . preprocess . parseFormula

-- Check if the formula is true
test :: String -> Bool
test = not . isEmpty . stringToAutomaton