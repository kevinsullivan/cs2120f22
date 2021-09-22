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
So, wow, we just gained a lot of insight!

true  →  true     true
true  →  false    false
false →  true     true
false →  false    true
-/


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

/-
Case analysis is a broadly useful proof
technique. Here we use it to prove true
→ true. We assume the premise, true and
have to show true. The true.intro rule 
will work, but let's instead try "case
analysis" on the assumed proof of true.
What we'll see is that there is only one
case (whereas with a proof of P ∨ Q, case
analysis presents two cases to consider.)
-/
example : true → true :=
begin
  assume t,
  cases t,
  exact true.intro,
end 

/-
The general principle is this: if we have
an assumed/arbitrary proof of X and need 
to show Y, we can try to do this by doing
case analysis on the proof of X. If we can
show that Y is true *in all cases* (in a
context in which we have *some* proof of 
X) then we have shown that Y must be true
in this context.
-/

/-
The most interesting example of the preceding
principle occurs when you're given or you can
derive a proof of false. For then all you have
to do to show that some proposition, P, follows
is to show that it's true for all possible ways
in which that proof of false could have been
constructed. Remember, there are two ways to
construct a proof of P ∨ Q, so case analysis 
results in two cases to consider; and one way 
to construct a proof of true, so there's only
one case to consider. Now, with a proof of false
there are *zero* ways to construct proof, *and
so there are zero cases to consider, and the
truth of your conclusion follows automatically!
-/

/-
Here we prove false → false again, but this
time instead of using the assumed proof of 
false to prove false, we do case analysis on
the given proof of false. There are no cases
to consider, so the proof is complete!
-/
example : false → false :=
begin
  assume f,
  cases f,    -- instead of exact f, do case analysis
end

/-
In fact, it doesn't matter what your conclusion
is: it will always be true in a context in which
you have a proof of false. And this makes sense,
because if you have a proof of false, then false
is true, so whether a given proposition is true 
or false, it's true, because even if it's false,
well, false is true, so it's also true!
-/

/-
Here, then, is the general principle for false
elimination: how you *use* a proof of false that
you have been given, that you've assumed, or that
you've derived from a contradiction (as we will
see).

The theorem states that if you're given any
proposition, P, and a proof, f, of false, then
in that context, P has a proof and is true.
Another way to think about what's going on here
is that if you have a proof of false, you are 
already in a situation that can't possible happen
"in reality" -- there is no proof of false -- so
you can just ignore this situation.
-/

theorem false_elim (P : Prop) (f : false) : P :=
begin
  cases f,
end

/-
The elimination principle for false is called 
false.elim in Lean. If you are given or can
derive a proof, f, of false, then all you have
to do to finish your proof is to say, "this is
situation can't happen, so we need not consider
it any further." Or, formally, (false.elim f). 
-/

example : false → false :=
begin
  assume f,
  exact false.elim f, -- Using Lean's version
end

