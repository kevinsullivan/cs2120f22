import .lecture_2

/-
From the axioms of reflexivity and substitutabilty
we now prove two *theorems*. A theorem is a proven
proposition. You can even think of the theorem as a
proof of a given proposition. A proof establishes a
conjecture as a theorem. And once it's a theorem,
you can use it like any other inference rule. In
this way, you can build up vast, layered libraries
of theorems. That's what we call mathematics. It's
what mathematicians do.

In this file, we provide both formal and informal
proofs of two theorems:

[1] Equality is symmetric.
[2] Equality is transitive.
-/

/-
To master these concepts, you must appreciate
the distinction between propositions and proofs.
Propositions are "statements of fact" that might
or might not be true. Proofs are objects that
show such propositions to be true. Propositions
that are not true, have no proofs (otherwise of
course they'd be true, as we just said).

So, first, you have to be able to *state* the
conjecture in the formal language of predicate
logic. We'll use an implementation of a specific
version of predicate logic provided by the Lean
Prover.

Second, you must understand how to construct 
proofs of such propositions, if proofs actually
exist, which they might or might not for given
propositions. Not all propositions, statements
asserting "facts", are true. The sky is magenta.
-/


/-
Theorems
-/

-- We define eq_symm to be the proposition at issue
-- Note: Prop is the type of all propositions in Lean
-- And each proposition is itself a type: of it proofs
def eq_symm : Prop := 
  ∀ (T : Type) 
    (x y : T), 
    x = y → 
    y = x 

-- We define eq_trans formally in the same basic way
def eq_trans : Prop := 
  ∀ (T : Type) 
    (x y z : T), 
    x = y → 
    y = z → 
    x = z

/-
Proofs
-/

/-
In the logic of Lean, a proposition is a type,
and the values of that type are its proofs. Just
as we can give an example value of an ordinary 
data type, such as ℕ, we can also give example
values of propositions acting as types, i.e., 
proofs.
-/

-- give a value of the nat type
example : ℕ := 5

-- give a proof of the proposition 1 = 1 
example : 1 = 1 := eq.refl 1

/-
We will now present formal proofs of our two 
theorems in this style.
-/

/-
Proof: equality is symmetric.
-/

example : eq_symm :=
begin
  unfold eq_symm, -- replace name with definition
  assume T x y e, -- assume arbitrary values
  rw e,           -- rw uses eq.subst to replace x with y
                  -- and then applies eq.refl automatically
  -- QED.
end

/-
Proof: equality is transitive.
-/

example : eq_trans := 
begin
  unfold eq_trans,
  assume T,
  assume x y z,
  assume e1,
  assume e2,
  rw e1,
  exact e2,
end

/-
A fundamental idea is that any proof is as good as any
other for establishing the truth of a proposition. Here
is an equally good alternative proof (or to be correct,
proof-generating scripts in the "proof tactic" language" 
of the Lean Prover.
-/

example : eq_symm :=
begin
  unfold eq_symm,   -- replace name with definition
  assume T x y e,   -- assume arbitrary values
  apply eq.subst e, -- apply axiom 2, substitutability
  exact eq.refl x,  -- apply axiom 1, reflexivity
  -- QED.
end

/-
There. That's a nice proof (script), as it closely
models a typical English language proof. To wit:

Theorem: Equality is symmetric.
Proof: Assume we're given arbitrary values of T, 
x, y, and a proof of x = y. What remains to be
proved is y = x. Apply substitutability to write
x as y or y as x. The result is trivially true 
by the reflexive property of equality.
-/