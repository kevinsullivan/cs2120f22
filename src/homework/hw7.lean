import data.set

namespace relation

/-
Preliminary set up. We specify a relation, r, 
as a two-place predicate on a type, β, with
notation, x ≺ y, for (r x y).
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  


/-
We define assymetric as a predicate on binary
relations. Lean's library doesn't define this,
surprisingly, so we include it here. Otherwise
in this file, you are using Lean's definition
of the properties of relations that we've been
learning about.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x



-- #1: Give both a formal and an English-language proof.
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
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

Try prove this version of the conjecture. If you get stuck, the
you need to figure out an additional condition that needs to be 
added as a premise to make the proposition true. In that case,
add the condition and then show that the conject is true.

#2
-/
example : transitive r → reflexive r → ¬ asymmetric r :=
begin
end



/-
You may use the following formal definition of the powerset 
of a set, s. Lean's libraries don't provide this definition.
-/
def powerset (s : set β) := { s' | s' ⊆ s}


/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof, of this proposition. Y
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
end


/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/

def divides (m n : ℕ) := ∃ k, n = k * m

/- 
#3: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/

-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
end

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
end

-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
end 

-- #D. prove that divides is transitive
example : transitive divides :=
begin
end 

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

-- Answer here

/- 
#F. Prove that divides is antisymmetric. Use our
anti_symmetric predicate on binary relations to state
the proposition formally.
-/
example : anti_symmetric divides := 
begin  
end


/- #4
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
begin
end

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
end

-- C
example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
end


end relation
