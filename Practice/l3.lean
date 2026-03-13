-- Operations on languages
-- Union, Intersect etc.
import Proofs.Lang

open Lang
open Lang.Examples

variable {Sigma : Type}

def union (L M : Lang Sigma) : Lang Sigma :=
{ w | w ∈ L ∨ w ∈ M }
-- Created variables L and M which are languages of Sigma (aka the same content sigma has)
-- Made a defintion where:
  --  A word is in union if its in L OR M

-- e.g.
-- L = words of only a’s
-- M = words of only b’s
-- L ∪ M = words of only a’s OR only b’s

def interscetion (L M : Lang Sigma) : Lang Sigma :=
{ w | w ∈ L ∧ w ∈ M }
-- A word is in intersection if its in L AND M


def complement (L : Lang Sigma) : Lang Sigma :=
{ w | ¬ w ∈ L }
-- A word NOT in L is a complement



def concatenation (L M : Lang Sigma) : Lang Sigma :=
{ w | ∃ u v, u ∈ L ∧ v ∈ M ∧ w = u ++ v }
-- Joining of two words together




-- Kleene Star
  --L* = any number of concatenations of L


inductive star (L : Lang Sigma) : Lang Sigma where
| empty : star L []
| step  : u ∈ L → v ∈ star L → star L (u ++ v)
-- L* is a concantenation of any instance including an empty set, one copy, two etc...
-- A word is in L* if is empty or is a word from L followed by another word in L*



-- ∃ u v = witnesses
-- Essentially instances of something
