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
We can now state the the general principle. If
you have a proposition, X (such as P ∨ Q) that has
several possible forms of proof, and you show that
in each and every one of thoses cases, some other
proposition R must be true then you've shown that
X → R, because you've shown a way to convert any
for of proof of X into a proof of R.
-/

/-
So now we're lined up for a mind-bending count-down.

As we've just said, there are two possible forms or
cases of proofs for a disjunction, so when we do case
analysis, we have to consider two cases. But now let's
consider proposition, true → true. To prove it we'll
start by assuming that we have a proof, t, of true. 
A case analysis on this proof has only one case: the
only way a proof of true can arise is by true.intro.
-/

example : true → true :=
begin
  assume t,   -- now we've assumed a proof of true
  cases t,    -- there's just one case to consider
  exact true.intro,   -- and it is easily proved
end 


/-
So now let's return to a proposition we already
proved to be true, but now use case analysis in
the proof.
-/
example : false → false :=
begin
  assume f,   -- assume we're given a proof, f, of false
  cases f,    -- case analysis on f; zero cases; done!
end

/-
Case analysis is the elimination principal
for false. If one can derive a proof of false,
what that really means is "this can't really
happen," so if you assume it does, then, really
anything goes. 
-/
example : false → false :=
begin
  assume f,             -- assumed proof of false (argument)
  exact false.elim f,   -- false.elim in Lean
end

/-
If you have a proof of false, then any proposition
is true!
-/
theorem false_elim (P : Prop) (f : false) : P :=
begin
  cases f,    -- try exact false.elim f
end

/-
Finally, now, we're in a position to see how to 
prove some not completely trivial propositions false.
Let's prove that it's false that 0 = 1. In other words,
let's prove, ¬0 = 1, I other words let's prove that
0 = 1 → false. The way forward is to assume that we
have a proof, say h, of 0 = 1, and then in this
context we need a proof of false! 

The only way to get there is to show false for
every possible form of proof of 0 = 1. But the only
form of proof of an equality is (eq.refl n). There
are *zero* forms of proof for the proposition 0 = 1.
A case analysis thus show that no matter which of
the *zero* forms of proof you have, you get false.
-/
example : ¬(0 = 1) :=
begin
  assume h, -- assume a proof, h, of 0 = 1
  cases h,  -- case analysis reveals this can't happen
  -- we thus have a proof that 0 = 1 has no proofs
end

