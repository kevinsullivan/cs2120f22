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
Ok, you actually have to *apply* the axiom of reflexive equality. 
-/

example : 1 = 1 := eq_refl ℕ 1  -- Our definition
example : 1 = 1 := @eq.refl ℕ 1 -- Lean, with inference turned off by @
example : 1 = 1 := eq.refl 1    -- Lean's definition  with T=ℕ inferred

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

-- EXAMPLES

-- a proposition and a predicate
def eq_3_3 : Prop := 3 = 3
def eq_n_3 (n : ℕ) : Prop := n = 3

-- predicates applied to values yield propositions
#reduce eq_n_3 2
#reduce eq_n_3 3
#reduce eq_n_3 4

-- 
axioms 
  (T : Type)      -- e.g., nat
  (P : T → Prop)  -- e.g., eq_n_3
  (x y : T)       -- arbitary nats
  (e : x = y)     -- a proof x = y
  (px : P x)      -- proof of is3 x

theorem deduction : P y := 
eq_subst T P x y e px -- e.g., proof is is3 y


/-
REFLEXIVITY OF EQUALITY
-/

/-
A binary relation is specified by a
two-place predicate. In other words,
you can think of it as a function that
takes two values and yields a proposition
about them. Equality is such a relation.
You can write x = y, but you can also
write eq x y to mean the same thing.
Writing it this way makes it clear
that equality takes two arguments
and returns a proposition.

Examples:
  eq 3 4 -- the proposition that 3 = 4
  eq 3 3 -- the proposition that 3 = 3

You can understand the following 
general explanation by taking eq as
a possible relation in place of "R"
in the following.
-/

-- We've already assumed T can be any type

-- Next assume we have an arbitrary binary relation, R, on T
axiom R : T → T → Prop

-- here's a formal definition of what it means for R to be reflexive
def rel_reflexive := ∀ (x : T), (R x x)

def rel_symmetric := ∀ (x y : T), (R x y) → (R y x)

def rel_transitive :=
  ∀ (x y z : T), (R x y) → (R y z) → (R x z)

/-
So now, from only our two axioms, let's prove that
equality is not only reflexive, but also symmetric
and transitive!
-/

/-
Theorem: *equality is symmetric*

Proof: We'll *assume* the premises of the conjecture:
that T is a type; x and y are values of that type; and 
it's true (and we have a proof, h) x = y. Now *in the
context* of these assumptions, we need to construct a
proof that y = x. We can do that by applying the axiom
of the substitutability of equals to the proposition
to be proved, using our proof of x = y as an argument,
to substitute y for x whereever x appears. The result
is that we must now only prove y = y. And that is done
by applying the axiom of reflexivity of equality.
-/

/-
Here's a formal proof. What's most important at this
point is that you be able to follow how the *context*
of the proof evolves as we make each of our "moves" 
in the construction of the final proof. Use SHIFT + 
CMD/CTRL + ENTER to open the Lean Information View,
which will present the evolving proof context, then
click on each line of the proof-constructing script
we've give you here to see how each move affects the
context.
-/
theorem eq_symm : 
  ∀ (T : Type) (x y : T), x = y → y = x :=
begin
  assume T,
  assume x y,
  assume h, 
  rw h,
  -- rw applies eq.refl automatically to complete the proof
end

/-
TRANSITIVITY OF EQUALITY

If x, y, and z are objects of some type, T, and we 
know (have proofs or axioms) that x = y and y = z,
then we can deduce (and have a proof) that x = z.
-/

theorem eq_trans : 
  ∀ (T : Type) 
    (x y z : T) 
    (e1 : x = y) 
    (e2 : y = z), 
  x = z :=
begin
  assume (T : Type), -- take as temporary axiom!
  assume (x y z : T), -- another one: context!
  assume (e1 : x = y),
  assume (e2 : y = z),
  rw e1,
  rw e2,      -- eq.refl applied automatically
end


