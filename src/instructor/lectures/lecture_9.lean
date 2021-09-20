/-
Negation
-/

/-
Given an proposition, P, we can form a new
proposition, usually written as ¬P, which we
pronounce as "not P," and which we define in 
such as way as to assert that P is not true.
-/

/-
So what does it mean when we say that *it is
true that P is not true*? 
-/

/-
First, if ¬P is true, there should be a proof
of it. Second, what that proof should show is 
that *there can be no proof of P*. 
-/

/-
So the way we're going to say ¬P is to say
if P were true then something that is completely
impossible would happen. Because the impossible
cannot happen, therefore there must be no proof
of P.
-/

/-
What we're going take as "the impossible thing"
is that there is a proof of false. Have defined
false to be exactly a proposition with no proofs
(otherwise it'd be true), so to have a proof of
false is an impossibility.)
-/

example : false → false :=
begin
  assume f,
  exact f,
end 

example : false → true :=
begin
  assume f,
  exact true.intro,
end 

example : true → true :=
begin
  assume t,
  exact true.intro,
end 

example : true → false :=
begin
  assume t,
  -- stuck
end



/-
It's this analysis that leads to the definition
of ¬P. For any proposition P, we *define* ¬P to
be the proposition, P → false. What this means 
is that if there is a proof of P → false, then
you can conclude (by definition) ¬P. This is the
introduction rule for ¬.
-/

#check not    -- see definition in Lean library

/-
So how do you prove P → false? It's just like any
other implication: *assume* that P is true and show
that with that you can construct a proof of false.
-/

/-
Example. Prove ¬ 0 = 1.
-/

example : false := 
begin
end

example : ¬ false := 
begin
  assume f,
  exact f,
end

example : ¬ (0 = 1) := 
begin
  assume h,
  
end


/-
To understand how to finish off this last
proof, we need to talk more case analysis
again. Remember that we've used it to reason
from a proof of a disjunction. Suppose we
want to know that P ∨ Q → R. We start by 
assuming that we have a proof, pq, of P ∨ Q, 
and then we need to show that R follows as
a logical consequence.

But there are exactly two possible forms that a
proof of P ∨ Q can take (or.intro_left p) and
(or.intro_right q), where p and q are proofs of
P and of Q, respectively. What we therefore need
to show is that no matter which of those two 
forms of proof we have, of P ∨ Q, that the truth
of R follows. So we do a case analysis on pq.

In the first case, we assume P ∨ Q is true
because P is (or.intro_left was used to create
the proof). In this case we need to show that 
P → R. In the second case, where P ∨ Q is true 
because Q is (or.intro_right was used to create
the proof of P ∨ Q), we need to show that Q → R.

The general principle is that if you can show
that a proposition, R, is true no matter which
form of proof you have of some proposition, X, 
then you have proven that X → R. This is the key
idea behind *proof by case analysis*. Show that
given any possible proof of P, that Q follows,
and that's what gives you a proof of P → Q. A
good start is to know just how many cases you
have to consider! Given  proof of P ∨ Q, how many
cases are there? Two.
-/

example : ∀ (P Q R : Prop), P ∨ Q → R :=
begin
  assume P Q R,
  assume pq,
  cases pq,       -- or elimination
                  -- stuck here of course
end

example : true → true :=
begin
  assume t,
  cases t,
end 


example : ¬(0 = 1) :=
begin
  assume h,
  cases h,
end

example : false → false :=
begin
  assume f,
  cases f,
end

example : false → false :=
begin
  assume f,
  exact false.elim f,
end

theorem false_elim (P : Prop) (f : false) : P :=
begin
  cases f,
end