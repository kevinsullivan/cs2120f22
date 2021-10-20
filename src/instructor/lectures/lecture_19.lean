import data.set

/- 
PART II: BASIC SET THEORY

Give formal and English language proofs of 
the following conjectures.
-/

def evens : set ℕ := { n | n%2 = 0}

example : ({ 0, 2 } : set ℕ) ⊆ evens :=
begin
  /-
  show ∀ n, n = 0 ∨ n = 2 → n ∈ evens,
  -/
  assume n,
  assume h,
  cases h,
  -- case: n = 0
  rw h,
  /-
  unfold evens,
  show {n : ℕ | n % 2 = 0} 0,
  show 0 % 0 = 0,
  -/
  exact rfl,
  -- case: n = 2
  cases h,
  /-
  show 2 ∈ evens,
  show evens 2,
  unfold evens,
  show 2 % 2 = 0,
  -/
  exact rfl,
end

/-
We now look at the concept of *equality* 
of sets. To show that two sets are equal,
e.g., L = X, we need to show that a value
is in L if and only if it's in X. This is
the same as showing L ⊆ X ∧ X ⊆ L. This
in turn means 
  ∀ x, 
    (x ∈ L → x ∈ X) ∧
    (x ∈ X → x ∈ L)
which we can also write as
  ∀ x, x ∈ L ↔ x ∈ X.
Now to get from a proof of that to a proof
of L = X requires a new axiom, the axiom 
of set extensionality. It just says that 
if we prove ∀ x, x ∈ L ↔ x ∈ X then we 
can, by applying the axiom, deduce that
L = X. The set extensionality axiom in 
Lean is called ext, defined in the set
namespace; so you can refer to it either
as set.ext, or you can open the set
namepace and then just call it ext. 
-/
#check @set.ext 

/-
Remember that you can think about an
implication, P → Q, in two ways: first,
if P then Q; second, to prove P it will
suffice to prove Q. So to prove L = X, 
it suffices to prove ∀ x, x ∈ L ↔ x ∈ X,
because one can then apply ext to that
proof to derive a proof of L = X. In 
other words, ext lets you "reduce" the
need for a proof of L = X to the need
for a proof of ∀ x, x ∈ L ↔ x ∈ X. And
that is what we see next. 

The concept of set equality, and the 
need to prove certain sets to be equal,
is extremely common, so it's important
to master these concepts here.
-/

example : ∀ {α : Type} (L X : set α), L ⊆ X → ((L ∩ X) = L) := 
begin
  intros α L X h,
  apply set.ext _,  -- turn = into ↔ using extensionality axiom
  -- that's the whole proof as long as we can fill in the _
  -- but now that's just ordinary logical reasoning
  assume x,
  split,
  -- forward
  assume h,
  cases h,
  exact h_left,
  -- backward
  assume k,
  exact and.intro k (h k),
end 

/-
Give an English language proof of the preceding theorem.
-/


/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/


/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/


/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof.
-/


/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof.
-/


/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There you will find definitions of left and right
distributivity, which you will need for the following
exercises.
-/

/-
Exercise: Prove (formally and informally) that 
∩ is left-distributive over ∩.
-/


/-
Exercise: Prove (formally and informally) that 
∪ is left-distributive over ∩.
-/


