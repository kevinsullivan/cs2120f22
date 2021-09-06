/-
In this file, we give formal statements (our version)
of the two axioms of equality. We also present Lean's
versions of these rules, and show how you can use them
without giving all of the arguments explicitly.
-/

/-
AXIOMS

Everything is equal to itself. A bit more formally,
if one is given a type, T, and a value, t, of this
type, then you may have a proof of t = t "for free."
-/

axiom eq_refl  : 
  ∀ (T : Type)  -- if T is any type (of thing)
    (t : T),    -- and t is thing of that type, T
  t = t         -- the result type: proof of t = t

/-
INFERENCE RULE #2/2: SUBSTITUTION OF EQUALS FOR EQUALS

Given any type, T, of objects, and any *property*, P,
of objects of this type, if you know x has property P
(written as P x) and you know that x = y, then you can
deduce that y has property P.
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
We will now present formal proofs of our two 
theorems in this style.
-/

/-
CONJECTURES
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
PROOFS: From conjectures to theorems
-/

/-
Proofs: equality is symmetric.
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

end

/-
INTRODUCTION and ELIMINATION RULES
-/

