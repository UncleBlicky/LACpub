import Proofs.Lang

open Lang
open Lang.Examples

inductive SigmaAB
| a | b
deriving DecidableEq, Fintype

#check SigmaAB
#check SigmaAB.a


inductive SigmaXYZ
| x | y | z | a | b | c
deriving DecidableEq, Fintype
-- Created an alphabet called SigmaXYZ with 6 elements
-- Made it equality derivable (a = b etc.) and gave the alphabet a finite amount of elements


def w1 : List SigmaAB := [SigmaAB.a, SigmaAB.b, SigmaAB.a]
#eval w1.length
#eval w1.count SigmaAB.a
-- Made a word from the defined alphabet
-- Counted the length of the word and how many symbols are in the alphabet

def w2 : List SigmaXYZ := [SigmaXYZ.a, SigmaXYZ.b, SigmaXYZ.y]
#eval w2.length
#eval w2.count SigmaXYZ.x
-- My turn




--Big conceptual jump!





def L_len2 : List SigmaAB → Prop
| w => w.length = 2
-- Have just defined a function called L_len2
-- Takes a list of symbols, SigmaAB (a Word)
-- Returns a proposition

--Inputs a word -> checks if its true or not -> Outputs true or false

-- The proposition being that the word (w) has a length of 2

example : L_len2 [SigmaAB.a, SigmaAB.b] := by rfl
-- Solves this proof by providing 2 symbols which are part of SigmaAB
-- The word has the length of 2 symbols



def hasA : List SigmaAB → Prop
| w => SigmaAB.a ∈ w
-- New function
-- All words inputed into this function hould have the symbol 'a'

example : hasA [SigmaAB.a, SigmaAB.a] := by simp [hasA]



def L_len2' : Set (List SigmaAB) :=
  { w | w.length = 2 }
  -- I have defined a set of lists (words) => a language
  -- Each word in this set contains 2 symbols
  -- { w | ... } ==> set-builder notation
  ----- Essentially telling lean the set of all w such that length = 2.

  example : [SigmaAB.a, SigmaAB.b] ∈ L_len2' := by rfl
  -- Prove the proof by just confirming this constructed word has 2 symbols then rfl cuz trivial



  def eqAB : Set (List SigmaAB) :=
  { w | w.count SigmaAB.a = w.count SigmaAB.b }
  -- In the word, 'a', must appear the same amount of times as 'b'.

  example : [SigmaAB.a, SigmaAB.b, SigmaAB.b, SigmaAB.a] ∈ eqAB := by rfl
    -- Proof



def onlyA : Set (List SigmaAB) :=
  { w | ∃ n, w = List.replicate n SigmaAB.a }

example : [SigmaAB.a, SigmaAB.a] ∈ onlyA := by
refine ⟨2, ?_⟩
rfl
