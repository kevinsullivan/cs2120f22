section pred_logic

variables X Y Z : Prop

/- *** NOT *** -/


-- ¬ 
/-
With an understanding of "false" and its elimination rule, we
can now talk about the inference rules for negation. 
-/

/-
Recall that if P is any proposition, then (not P), generally 
written as ¬P, is also a proposition. when is ¬P true? It's
true in first-order logic if P is false. It's also true in
constructive logic when P is false, which is to say, *when 
there is no proof of P*. 

Now here's the slightly tricky way that we show that there can
be no proof of P. We show (P → false). What this proposition
says is that "If there is a proof of P, then from it we can
derive a proof of false." But a proof of false doesn't exist,
so if we prove (P → false) is true then there must be no proof
of P. In other words, to prove there is no proof of P, we prove
P → false! And that leads to our definition of ¬P. What it means
is *exactly* P → false. 
-/
def not_ (X : Prop) := X → false  -- the definition of "not" (¬)

/-
Examples
-/

example : 0 = 1 → false :=
begin
assume h,   -- suppose 0 = 1
cases h,    -- that can't happen, no cases, we've proved ¬(0=1)
end 

example : ¬(0 = 1) :=
begin 
assume h,
cases h,
/-
Remember!!!  0 ≠ 1 means ¬(0 = 1) means 0 = 1 → false. You 
must remember that when you want to prove ¬P, that means you
need to prove P → false: that a proof of P is a contradiction.  
to remember this, because it tells you how to prove it. To
show it, assume the premise, 0 = 1, then show that in this
context, there is a contradiction ---given our intuitive
grasp of equality and the natural numbers. 

If you can derive a contradiction, that is tantamount to a 
proof of false, and from a proof of false, f, the truth of
any other proposition follows. Put another way, in terms of
Lean's formal logic, the term, (false.elim f), where f is a
proof of false, serves is a formal proof of any proposition.
-/
end

/- PROOF BY NEGATION 

What we have now seen is a crucial "proof strategy" often 
called proof by negation. To show ¬P, that the statement, 
P is false, is true, prove P → false. First assume that 
P is true (you have a proof of it) and show that in this
context, you can derive a proof of false. You will often
do this by producing a contradiction, which is proofs of
both X and ¬X for some proposition, from which, as we will
see shortly, you can derive a proof of false by applying
the rule of arrow elimination (function application!).  
-/

/-
HW #3 Exercise: state and prove the rule (the "theorem") 
of "no contradiction:" first in English and then in the
predicate logic of Lean. Or if you prefer, work it out 
in Lean and the write it in English. The formal statement
of the proposition is in the partially completed theorem 
below. 
-/

/-
English. Prove ¬(X ∧ ¬X), where X is any proposition.
This theorem states that it cannot be the case that 
both X and ¬X are true.

Proof by negation: Assume that (X ∧ ¬X) is true. By
use of and elimination deduce X and ¬X separately. 
But this is a contradiction, so the assumption must
have been false. Therefore ¬(X ∧ ¬X) is proved. QED.
-/

theorem no_contradiction : ¬(X ∧ ¬X) :=
begin
assume h,           -- where h proves (X ∧ ¬X)
cases h with x nx,  -- applies and elimination 
exact (nx x),       -- (nx x) is a proof of false
end

def excluded_middle   := X ∨ ¬X   -- not an axiom in CL
def neg_elim          := ¬¬X → X  -- depends on axiom of e.m.

/-
Exercises: Prove that the following propositions are theorems
(that they have proofs). Express your proofs in English. For
extra credit, provide formal proofs in Lean. Hint: Working out
the proofs in Lean can be a big help to expressing them in 
English.
-/

-- prove that these propositions are 
def contrapostitive   := (X → Y) → (¬Y → ¬X)
def demorgan1         := ¬(X ∨ Y) ↔ ¬X ∧ ¬Y
def demorgan2         := ¬(X ∧ Y) ↔ ¬X ∨ ¬Y


end pred_logic