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
there are no proofs of P*. 

Now here's the slightly tricky way that we show that there can
be no proof of P. We show (P → false). What this proposition
says is that "If there is a proof of P, then from it we can
derive a proof of false," which is a contradiction, because 
proof of false doesn't exist. So if we prove that (P → false) 
is true then there must be no proof of P. In other words, to 
prove there is no proof of P, we prove P → false, which is how
we define ¬P. ¬P is true iff P → false.  
-/

-- Here's how ¬X is defined (Lean already defines "not")
-- And not that ¬X just means (not X), which means X → false.

def not_ (X : Prop) := X → false  -- the definition of "not" (¬)

/-
Examples
-/

example : 0 = 1 → false :=
begin
assume h,   -- assume 0 = 1; this can't happen, of course
cases h,    -- there are no cases to consider, so NOT (0=1)
end 

/-
Here's exactly the same proposition but using ¬ notation
-/
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
called proof by negation. To show ¬P (that P is false), we
prove P → false. How? assume P is true and show that from 
this assumption you can derive a contradiction, something 
that cannot be, such as proof of false. 
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


/- PROOF BY CONTRADICTION 

First, recall that in proof by negation, we prove ¬P by 
assuming that P is true, deriving an impossibility, and
then concluding ¬P.

Proof by contradiction is just a tad more complicated. In
this proof strategy we prove P (rather than ¬P) by assuming
¬P (rather than P) and showing that *this* assumption leads
to an impossibility, a contradiction. What that proves is 
that ¬P must be false, which is to say, ¬¬P. Finally, from
there, we conclude P using *negation elimination*. This rule
is simply this (recall that we introduced X as an arbitrary 
propostion above):
-/

def neg_elim          := ¬¬X → X

/-
As a silly but simple example, let's prove that 0 = 0 using
the strategy of proof by contradiction.

Goal: Prove 0 = 0.
Proof (by contradiction). Assume h: ¬(0 = 0). Recall that 
this means h is a proof of (0 = 0) → false. But 0 = 0 is
true, so there is a proof of it, let's call it pf. Now we
simply apply h to pf (arrow elimination) to derive a proof
of false. By ¬ introduction, this proves ¬¬(0 = 1). Finally
we apply negation elimination to deduce that (0 = 1) is true. 
-/


/-
In Lean, "by_contradiction" is the name of the negation 
elimination rule. Because it relies on a non-constructive
assumption, it's tucked away in a module called classical. 
We can use it by referring to classical.by_contradiction.
The @ sign here is a detail you can ignore for now. It
just tells Lean to report the rule as its' written where
it's defined.

-/
#check @classical.by_contradiction
-- ∀ {p : Prop}, (¬p → false) → p
-- in other words, ∀ (P : Prop), ¬(¬P) → P
-- Proof by contradiction is application of ¬ elimination!

/-
Here's a formal proof-/
example : 0 = 0 :=
begin
apply classical.by_contradiction,
assume h,
let k := eq.refl 0,   -- (eq.refl 0) is a proof of 0 = 0
apply false.elim (h k),
end

/-
As a final wonderful point, it turns out that the law of
the excluded middle is also non-constructive, and if you
assume it, that will suffice to make negation elimination
valid again.
-/

#check @classical.em
-- em : ∀ (p : Prop), p ∨ ¬p

/-
The crucial point about the law of the excluded
middle is that (because it's a universal generalization)
you can apply it to any proposition, P, to get a "free" 
proof of P ∨ ¬P *on which you can then do case analysis*. 
Accepting the law of the excluded middle suffices to
prove the validity of negation elimination, ¬¬P → P,
and thus to use proof by contradiction in an otherwise
constructive logic. 
-/

-- If we assume em, then negation elimination is valid
example : 
  ∀ (P : Prop),   -- for any proposition P
    (P ∨ ¬P) →    -- if em is valid
    (¬¬P → P)     -- then neg elim is valid
                  -- and thus proof by contradiction
  := 
begin
assume P em_P,
assume nnp,
cases em_P,
-- case P
assumption,
-- case ¬P
contradiction,
end

/-
It also turns out that if you assume negation elimination 
(¬¬P → P) is valid, then you can prove excluded middle 
(∀ (P : Prop), P ∨ ¬P). The truth then is that each of 
these two axioms are equivalent in constructive logic.
-/

theorem em_equiv_pbc : 
  ∀ (P : Prop), (P ∨ ¬P) ↔ (¬¬P → P) := 
begin
_         -- challenge problem, on your own, optional
end

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