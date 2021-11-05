import ..instructor.lectures.lecture_23

namespace relation

/-
Define relation, r, as two-place predicate on 
a type, β, with notation, x ≺ y, for (r x y). 
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  
-- Strangely Lean's library does define asymmetric, so here it is.
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x



-- Prove both formally and in English.
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  unfold asymmetric reflexive,
  assume ex assym,
  assume refl,
  cases ex with b pf,
  have rbb : r b b := refl b,
  have contra := assym rbb,
  contradiction,
end



/-
Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. Is it actually true?
If not, what condition needs to be added to make it true? See
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html
-/
example : (∃ (b : β), true) → transitive r → reflexive r → ¬ asymmetric r :=
begin
  unfold transitive reflexive asymmetric,
  assume b trans refl,
  assume assym,
  cases b,
  have rbb := refl b_w,
  have nrbb := assym rbb,
  contradiction,
end



/-
State and prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and then give
an informal proof, of this proposition. You may use the following
formal definition of the powerset of a given set, s. 
-/

def powerset (s : set β) := { s' | s' ⊆ s}

example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  assume s s1 s2,
  assume s1ins s2ins,
  assume s1s2 s2s1,
  apply set.ext,
  assume x,
  split,
  assume xs1,
  -- you do the rest
end

/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/

def divides (m n : ℕ) := ∃ k, n = k * m

/- 
#3: Formally state and prove each of the following propositions.
Remember that the ring tactic is useful for producing proofs of
algebraic equalities involving + and *. You can use the phrase,
"by basic algebra" when translating the use of this tactic into
English.
-/

-- 3a: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
end

-- 3b. For any n, n divides n
example : ∀ n, divides n n :=
begin
end

-- #3c. prove that divides is reflexive 
example : reflexive divides :=
begin
end 

-- #3d. prove that divides is transitive
example : transitive divides :=
begin
end 

/- 
#3d. is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

-- Answer here

/- 
#3e. Prove that divides is antisymmetric. Use the
anti_symmetric predicate to state the proposition
formally.
-/
example : anti_symmetric divides := 
begin  
end


example : asymmetric r → irreflexive r :=
begin
end

example : irreflexive r → transitive r → asymmetric r :=
begin
end

example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
_


end relation
