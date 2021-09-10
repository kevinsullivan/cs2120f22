/-
In this file, we give formal statements (our version)
of the two axioms of equality. We also present Lean's
versions of these rules, and show how you can use them
without giving all of the arguments explicitly.
-/

/-
INFERENCE RULE #1/2: EQUALITY IS REFLEXIVE

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