/-
INTRODUCTION and ELIMINATION RULES
-/

/-
For ∀ x, P x (every x has property P)
  - introduction rule: assume arbitrary x, then show P x
  - elimination rule: *apply* a proof of ∀ x, P x, as a 
  kind of function to a specific value of x, say k, to 
  produce a proof of P k.
-/

theorem silly : ∀ (n : ℕ), true :=
begin
  assume (n : ℕ),
  exact true.intro, 
end

/-
The proposition true is unconditionally true,
as proven by an always available proof called
(in Lean) true.intro.
-/

#check silly 7

/-
The check command will tell you the type of any
expression (aka term) in Lean. Here we can see 
that silly is like a function, and that when we
apply it to the specific argument, 7, we get back
a proof of the resulting proposition (which is 
just, "true"). We'll soon be equipped to deal
with more interesting "return types".
-/

/-
For P → Q (if P is true then Q must also be true)
- introduction rule: assume arbitrary P, then show Q
- elimination rule: *apply* a proof of P → Q, as a
kind of function, to any proof of P to derive a proof of Q!
-/

lemma foo : ∀ (x : ℕ), x = 0 → x + 1 = 1 := 
begin
  assume x h,
  rw h,
end

/-
Wow! ∀ and → sure do seem similar. Indeed they're the same!
They define function types. We construct a proof of ∀ or → 
by assuming the premise and showing that in that context we
can derive a result of the conclusion type. We can then use
a proof of a ∀ or → by treating it as a function that can
be applied to a specific value to derive a proof *for that
specific value. Indeed, in Lean, → is really just another
notation for forall!
-/

/-
Introduction rule for and ∧

Give a proof of P and a proof of Q 
get back a proof of (P ∧ Q). 
-/

axioms (P Q : Prop)

#check P
#check (P ∧ Q)

axioms (p :P) (q : Q)

example : P ∧ Q := and.intro p q

/-
Prove that if arbitary propositions P and Q
are true (which is to say that we have a proof
of each of them), that the proposition P ∧ Q
is also true.
  
Proof: The conjecture that P ∧ Q is true
is proved by application the introduction 
rule for and.
-/

example : 0 = 0 ∧ 1 = 1 :=
begin
  apply and.intro _ _,
  apply eq.refl 0,
  apply eq.refl 1,
end 

theorem bar : 0 = 0 ∧ 1 = 1 :=
begin
  apply and.intro (eq.refl 0) (eq.refl 1),
end 

#check bar

#check and.elim_left bar
#check and.elim_right bar

theorem and_commutative : ∀ (P Q : Prop), P ∧ Q → Q ∧ P :=
begin
  assume P Q h,
  apply and.intro _ _,
  apply and.elim_right h,
  apply and.elim_left h,
end