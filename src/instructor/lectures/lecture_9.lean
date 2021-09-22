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
true that P is not true*? Or, equivalently, "it
is true that P is false?" 
  
Clearly we don't mean that the proposition P 
*is* (equal to) the proposition, *false*. No,
in this sense of false, what we mean by P is
false is that there are no proofs of P, so we
have to *judge* it to be logically false. We
distinguish between truth judgments and the
proposition, true.
-/

/-
So what we mean by ¬P is that there is no 
proof of P. The trick is now in how to show
that there can be no proof of P. We prove
it somewhat indirectly by proving P → false. 

Suppose P → false is true. What this says is
that if P is true then false is true. But the
latter is absurd because we've defined false
to the proposition with no proofs, so it can't
be true.

So if P → false is is true, then the consequence 
of that is that there *can be no proofs of P*. 
-/

/-
So let's launch a little exploration of proofs 
involving false and proofs of false.
-/

/-
First, what's your intuition? Is the follow 
proposition true or false? 

  false → false 

We'll let's see what happens when we try to 
prove it. What the implication says is that
*if* false is true, then false is true. To
prove it, assume false is true and that we
have a proof of it, f. All that remains is
to produce a proof of false: just f itself.
-/
example : false → false :=
begin
  assume f,
  exact f,
end 

/-
Does false imply true? If the impossible happens, 
is true still true? Turns out it is. Assume we've
got a proof that false is true. Now all we have to
do is to produce a proof of true. But it's an axiom
that there is one: in Lean called true.intro. So
it's true that false is true!
-/
example : false → true :=
begin
  assume f,
  exact true.intro,
end 

/-
Does true imply true? This one's easy as they get.
-/
example : true → true :=
begin
  assume t,
  exact true.intro,
end 


/-
Finally, does true imply false? Can you turn
any proof of true somehow into a proof of false?
If so, you have a proof of true → false. But the
answer is no. Suppose you have a proof of true.
Well, it's of no use at all in deriving a proof
of false, and in fact you can never derive one
from true premises, because our logic is sound(*).

-/
example : true → false :=
begin
  assume t,
  -- stuck: *there is no proof of false*
end

/-
So, wow, we just gained a lot of insight!

true  →  true     true
true  →  false    false
false →  true     true
false →  false    true
-/


/-
Having built some intuition, let's get back to 
the meaning of ¬P. For any proposition, P, we 
*define* ¬P to be the proposition, P → false. 
So ¬P is true exactly when P → false is true, 
and that is true exactly when P is false, when
there are no proofs of it. If you can produce a
proof of P → false, then you can conclude ¬P. 
This is the introduction rule for ¬.
-/

#check not    -- see definition in Lean library

/-
So how do you prove P → false? It's just like any
other implication: *assume* that P is true and show
that with that you can construct a proof of false.
-/

/-
Example. Prove ¬ 0 = 1.

Ok, we'll let's make another little diversion.
-/

example : false := 
begin                     -- no way to prove this 
end

example : ¬ false := 
begin
  assume f,               -- REMEMBER: ¬P *means* P → false, so *assume* P, show false.
  exact f,
end

example : ¬ (0 = 1) := 
begin
  assume h,
  -- what do we do now?
end


/-
To understand how to finish off this last
proof, we need to talk about *case analysis*
again. Remember that we used it to reason
from a proof of a disjunction. Suppose we
want to know that P ∨ Q → R. We start by 
assuming that we have a proof, pq, of P ∨ Q, 
then we need to show that R follows from
the truth of P ∨ Q as a logical consequence.

But to know whether R follows from P ∨ Q, we
need to know that it follows from each of them.
Well, there are exactly two possible forms that 
a proof, pq, of P ∨ Q can take (or.intro_left p)
and (or.intro_right q), where p and q are proofs
of P and of Q, respectively. What we therefore 
need to show is that no matter which of the two
cases, a proof of R follows. 

The rest of the proof is by case analysis on
the proof, pq, of P ∨ Q. In the first case, we
assume P ∨ Q is true because P is (or.intro_left 
was used to create the proof). In this case we
need to show that  P → R. In the second case,
P ∨ Q is true because Q is (or.intro_right was
used to create the proof of P ∨ Q. Now we need
to show that having a proof of Q gets us to a 
proof of R, i.e., that Q → R.
-/


-- template: proof of disjunction by case analysis
example : ∀ (P Q R : Prop), P ∨ Q → R :=
begin
  assume P Q R,
  assume pq,      -- assuming we have a proof, (pq : P ∨ Q)
  cases pq,       -- proceed by case analysis
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

