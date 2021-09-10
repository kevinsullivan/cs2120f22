/-
We've seen that logics start with axioms that
can then be combined (with other information)
using *inference rules* to derive theorems. In
this file we review what we've covered so far
and then we introduce:

(1) The concept of introduction and elimination
rules for a given logical construct.
(2) We distinguish the reflexivity axiom as an
*introduction* rule (one that produces a proof
of an equality), and the substitutability of
equals as an *elimination* rule (one that uses,
or consumes) a proof of an equality to produce
some other kind of result.
(3) We explicitly identity the introduction 
rules for ∀ and for →. To produce a proof of
∀ (x : T), P x (where T is a type and P is a
predicate that asserts some property of x), we
*assume* that we're given an arbitrary but
specific (x : T) ["x of type T"], and then 
we prove (P x) *for that x*. Because we made
no assumptions whatsoever about x, if we can
show that (P x) is true, then it must be true
*for all* (x : T).
-/

/-
Introduction rule for equality. 
-/

axiom eq_refl  : 
  ∀ (T : Type)  -- if T is any type (of thing)
    (t : T),    -- and t is thing of that type, T
  t = t         -- the result type: proof of t = t

/-
Elimination rule for equality.
-/
axiom eq_subst : 
  ∀ (T : Type)      -- if T is a type
    (P : T → Prop)  -- and P is a property of T objects
    (x y : T)       -- and x and y are T objects
    (e : x = y)     -- and you have a proof that x = y
    (px : P x),     -- and you have a proof that x has property P
  P y               -- then you can deduce (and get a proof) of P y

/-
The Lean versions of these axioms are called eq.refl and eq.subst.
They're defined in ways that allow (and require) one not to give the
T, P, x, or y parameters explicitly when applying eq_subst. More
details come later.
-/

/-
CONJECTURES (review)
-/

-- A conjecture: equality is symmetric.
def eq_symm : Prop := 
  ∀ (T : Type) 
    (x y : T), 
    x = y → 
    y = x 

-- A conjecture: equality is transitive.
def eq_trans : Prop := 
  ∀ (T : Type) 
    (x y z : T), 
    x = y → 
    y = z → 
    x = z


/-
PROOFS: From conjectures to theorems
-/


example : eq_symm :=
begin
  unfold eq_symm, -- replace name with definition
  assume T x y e, -- Introduction rule for ∀
  rw e,           -- Elimination rule for =
  -- QED.
end

/-
A different proof, now using eq.subst explicitly.
Any proof of a proposition is as good as any other
for showing the truth of a proposition. We do not
care what proofs you give, as long as they're correct
(unless stated otherwise).
-/

example : eq_symm :=
begin
  unfold eq_symm,   -- replace name with definition
  assume T x y e,   -- introduction rule for ∀ 
  apply eq.subst e, -- elimination rule for =
  exact eq.refl x,  -- introduction rule for =
  -- QED.
end

/-
Review: Proof: equality is transitive.
-/

example : eq_trans := 
begin
  unfold eq_trans,
  assume T x y z e1 e2, -- introduction rule for ∀ 
  rw e1,                -- elimination rule for =
  exact e2,
end

/-
Note: Lean defines these rules as
- eq.refl
- eq.subst
- eq.symm
- eq.trans
-/

/-
Practice
-/

example : ∀ (T : Type) (x y z : T), x = y → y = z → z = x :=
begin
  assume T x y z h1 h2, -- introduction rule for ∀ 
  apply eq.symm _,      -- application of symm *theorem*
  apply eq.trans h1 h2, -- application of trans theorem
end

/-
INTRODUCTION and ELIMINATION RULES
-/

/-
For =
  - introduction rule: eq.refl 
  - elimination rule: eq.subst
-/

/-
For ∀ x, P x
  - introduction rule: assume arbitrary x, then show P x
  - elimination rule: next time!
-/

/-
For P → Q
- introduction rule: assume arbitrary P, then show Q
- elimination rule: next time.
-/

