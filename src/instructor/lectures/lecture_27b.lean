import .lecture_25

/-
BASIC SETUP
-/
namespace relations
section relation

/-
Define relation, r, as two-place predicate on 
a type, β, with notation, x ≺ y, for (r x y). 
-/
variables {α β γ : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  

/-
The point of this file is to give you an extended
example of interleaving a fluent natural language
proof with steps in a tactic script that produces
a "mechanically verified proof object". You want 
to communicate the critical steps in your reasoning 
in English but at a level of abstraction where it
can be ok to elide certain details.

So here we interleave elements of a formal proof
and a corresponding English language proof. Knowing
how to reason in precisely logically correct ways is
crucial, and then being able to express those ideas 
in fluent, to-the-point, natural language proofs is
the next essential skill. Eventually you will reason
fluently, confident that the underlying details are
all fine. That's really the goal: to think fluently
and validly about conjectures and proofs in math and
logic.

You should first study the conjecture to be proved,
then follow the sequence of proof states defined by 
the following formal proof-generating tactic script
to see exactly why the conjecture is true for any r.

Once you understand the formal argument, go through 
the proof again, but now look carefully at each of
the associated English utterances. String these all
together and you'll have a quite good first draft 
of an English language proof.
-/
example : (∃ b: β, true) → asymmetric r → ¬ reflexive r :=
begin
  assume e,   -- suppose β is inhabited
  assume a,   -- and r is asymmetric
              -- now show r is not reflexive
  assume x,   -- proof by negation: assume it is
              -- ... and show a contradiction 

  /- 
  We start by expanding the definitions 
  of asymmetric and reflexive: 
  -/
  unfold asymmetric at a,
  unfold reflexive at x,

  /-
  Our assumption that β is inhabited gives
  us some witness (w : β)
  -/
  cases e with w _,
  
  /-
 Applying reflexivity of r to w proves r w w,
 that w is related to itself.
  -/
  have rww := x w,
  
  /-
  Applying asymmetry to r w w derives ¬ r w w. 
  -/
  have c := a rww,
  
  /-
  This contradiction shows that the assumption
  that r is reflexive cannot have been correct
  in the prevailing context, as it has gotten us
  into a situation that never actually occur. It
  by non-contradiction it isn't possible to have
  both r w w and ¬ r w w.
  -/
  contradiction,

  /-
  We've thus proved that an asymmetric
  relation over a non-empty set cannot
  be reflexive, which is what we set out
  to prove, for any relation r on objects
  of any type, β.  
  -/

-- QED
end

/-
-- suppose β is inhabited
-- and r is asymmetric
-- now show r is not reflexive
-- proof by negation: assume it is
-- and we will now show a contradiction

First we expand the definitions of 
asymmetric and reflexive. What we
are now to show is that the following
set of assumptions is inconsistent:
β: Type
r: β → β → Prop
e: ∃ (b : β), true
a: ∀ ⦃x y : β⦄, r x y → ¬r y x
x: ∀ (x : β), r x x

There is a contradition.
From e, infer a witness w : β.
Applying reflexivity (x), to w, 
we deduce r w w. Next, applying 
asymmetry (a), to r w w gives
¬ r w w, a contradiction. 
QED.
-/

end relation
end relations