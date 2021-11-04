import data.set

/-
1. Exercise: Prove that for any set, L, L ∩ L = L.
-/

theorem self_intersect 
  (β : Type) 
  (L: set β) :
  L ∩ L = L :=
begin
/-
By set extensionality it will suffice to 
have a proof of L ∩ L ↔ L.
-/
apply set.ext,

/-
To prove it, first assume that we have an
arbitrary value, x.
-/
assume x,

/-
What now have to prove the biimplication
in each direction: if x ∈ L ∩ L then it's 
in L, and if x ∈ L then it's in L ∩ L. 
-/
split,


/-
We'll start with the forward direction by
assuming that x ∈ L ∩ L.
-/
assume h,

/- 
By the definition of ∩, this means x ∈ L and 
x ∈ L. If that's true then certainly x ∈ L 
(by ∧ elimination--but leave out these kinds
of logical reasoning details now). We have
thus proven x ∈ L ∩ L → x ∈ L.
-/
cases h with l r,
assumption,

/-
Now the reverse: x ∈ L → x ∈ L ∩ L. 

Assume x ∈ L and show is that x ∈ L ∩ L.
-/
assume h,

/-
But that is true by the definition of ∩. 
x ∈ L ∩ L means (x ∈ L) and (x ∈ L). This 
in turn is true by the definition of and.
This proves (x ∈ L) → (x ∈ L ∩ L), finishes 
the proof of (x ∈ L) ↔ (x ∈ L ∩ L). And
by set extensionality we have  = L ∩ L.
-/
apply and.intro h h,

-- QED.
end

/-
2. Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/

theorem union_comm : 
  ∀ (β : Type) 
  {s1 s2 : set β},
  s1 ∪ s2 = s2 ∪ s1 :=
begin
  intros,
  apply set.ext _,

  intro,
  split,

  -- forward
    assume h,  
    -- by case analysis of h
    cases h,
      exact or.inr h,
      exact or.inl h,

  -- backward
    assume h,
    cases h,
      exact or.inr h,
      exact or.inl h,
end


/-
Proof: To show that ∩ is commutative, we need
to show that for all sets, A and B, and for all
objects o, o ∈ A ∩ B ↔ o ∈ B ∩ A. Suppose that
an object o is in A ∩ B. Then by the definition
of ∩, it is in A *and* it is in B. As and is 
itself commutative, o ∈ B *and* o ∈ A, so o ∈
B ∩ A. The reverse proof is true by the same
reasoning. The bi-implication holds, and it in
turn suffices to prove the equality that we
were to show. QED.
-/


/-
3. Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/

theorem subset_refl_trans : 
  ∀ (β : Type) (S L X: set β),
  (S ⊆ S) ∧ ((S ⊆ L) → (L ⊆ X) → (S ⊆ X)) :=
begin
  intros,
  split,  -- apply and.intro _ _,
  -- left side of ∧
  assume x h,
  assumption,
  -- right side of ∧ 
  assume h k,
  assume v n,
  have l := h n,  -- modus ponens
  have x := k l,  -- modus ponens
  assumption,
end

/-
To show (S ⊆ S) ∧ ((S ⊆ L) → (L ⊆ X) → (S ⊆ X)), 
it will suffice to prove (S ⊆ S) and S ⊆ L) → 
(L ⊆ X) → (S ⊆ X). To show S ⊆ S, it will suffice
(by the definition of ⊆) to show ∀ o, o ∈ S → o ∈ S.
To prove that, assume o is an arbitrary object and
that o ∈ S. The conclusion, o ∈ S, is now true by
assumption. So ∀ o, o ∈ S → o ∈ S, and this is the
very definition of S ⊆ S. 

We now turn to the second conjunct. We are to show
that (S ⊆ L) → (L ⊆ X) → (S ⊆ X). To prove it, we
assume that (S ⊆ L) and (L ⊆ X) and we need to show
that S ⊆ X. By the definition of ⊆, we have to show
that ∀ o, o ∈ S → o ∈ X. To prove this we assume 
that o is an arbitrary object and that o ∈ S, and
we must show o ∈ X. Combining o ∈ S with S ⊆ L, we
can conclude that o ∈ L (again by applying the
definition of ⊆). Combining this fact with the 
fact that L ⊆ X, we can conclude that o ∈ X. We
have thus showing that for any object, o, if o ∈ S
then o ∈ X, which is the definition of S ⊆ X, so
⊆ is transitive.


-/


/-
4. Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/

lemma inter_assoc : 
  ∀ {β : Type} 
    (a b c: set β),
  (a ∩ b) ∩ c = a ∩ (b ∩ c) :=
begin
  intros,
  apply set.ext,
  assume x,
  split,

  -- forward
  assume h,
  cases h with l r,
  cases l with ll lr,
  exact and.intro ll (and.intro lr r),

  -- backward
  assume h,
  cases h with l r,
  cases r with rl rr,
  exact and.intro (and.intro l rl) rr,
end
  
lemma union_assoc : 
  ∀ {β : Type} 
    (a b c: set β),
  (a ∪ b) ∪ c = a ∪ (b ∪ c) :=
begin
  intros,
  apply set.ext,
  assume x,
  split,

  -- forward
  assume h,
  cases h with l r,
    cases l with ll lr,
      -- x ∈ a
      exact or.inl ll,
      -- x ∈ b
      exact or.inr (or.inl lr),
      -- x ∈ c
      exact or.inr (or.inr r),

  -- backward
  assume h,
  cases h with l r,
  -- x ∈ a
  apply or.inl _, -- what is associativity of ∨?
  apply or.inl _,
  assumption,
  -- x ∈ b ∪ c
  cases r with l r,
    -- x ∈ b
    apply or.inl _,
    exact or.inr l,
    -- x ∈ c
    apply or.inr _,
    assumption,
end

theorem inter_and_union_assoc : 
  ∀ (β : Type)
    (a b c: set β), 
    (a ∪ b) ∪ c = a ∪ (b ∪ c) ∧ 
    (a ∩ b) ∩ c = a ∩ (b ∩ c)
  :=
begin
  intros,
  split,  -- applies and.intro in this context
  exact union_assoc a b c, -- univ specialization
  exact inter_assoc a b c, -- univ specialization
end

/-
This example illustrates an important point:
it is often very helpful to prove a few mini-
theorems, which we call lemmas, in a bottom-up
manner, that can then be combined to give the
desired overall proof.
-/

/-
Assignment: read (at least skim) the Sections 1 and 
2 of the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state, and prove, formally and 
informally, that ∩ is left-distributive over ∩.
-/

theorem inter_left_over_inter :
  ∀ {β : Type}
  (a b c : set β),
  a ∩ (b ∩ c) = (a ∩ b) ∩ (a ∩ c) :=
begin
intros,
apply set.ext,
assume x,
split,

assume h,
cases h with xa xbc,
cases xbc with xb xc,
exact and.intro (and.intro _ _) (and.intro _ _)
-- etc
end


/-
Exercise: Formally state and prove, formally and 
informally that ∪ is left-distributive over ∩.
-/

theorem union_left_over_inter :
  ∀ {β : Type}
  (a b c : set β),
  a ∩ (b ∩ c) = (a ∩ b) ∩ (a ∩ c) :=
begin
  intros,
  apply set.ext,
  assume x,
  split,

  assume h,
  cases h with xa xbc,
  cases xbc with xb xc,
  apply and.intro,
  apply and.intro,
  exact xa,
  exact xb,
  split,
  exact xa,
  exact xc,

  -- etc.
  admit,
end



example : ∀ {α : Type} (a: α) (L M N: set α), L ⊆ M ↔ (a ∈ L → a ∈ M) :=
begin
  intros,
  split,

  assume h k,
  exact h k,
  assume h,
  assume x xl,
  -- stuck
end

example : ∀ {α : Type} (L M: set α), L ⊆ M ↔ ∀ (a : α), (a ∈ L → a ∈ M) :=
begin
  intros,
  split,
  assume h,
  assumption,
  assume h,
  assumption,
end