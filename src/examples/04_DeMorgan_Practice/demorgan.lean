def dm1 : Prop := ∀ (A B : Prop), ¬ (A ∧ B) ↔ ¬A ∨ ¬B

example : dm1 :=
begin 
unfold dm1,                 -- unfold definition of dm1
assume A B,                 -- assume A, B are arbitrary props
apply iff.intro _ _,        -- by iff.intro it will suffice to prove → in both directions
/-
It's super-important to realize that the proof is *done*
except for the need to provide the two smaller proofs to
fill those "holes" marked by underscores above. You have
thus reduced the task of proving the overall theorem to 
the task of proving these two "lemmas." So now we turn to
the lemmas.
-/

-- Lemma 1: The forward implication is valid.

assume h,     -- assume the hypothesis, now show conclusion

-- Prove the conclusion by case analysis on classical 
-- truth/falsity of each of A, B
cases (classical.em A) with a na,   -- case analysis on truth of A
cases (classical.em B) with b nb,   -- "nested" case analysis on B

/-
Two cases for B, assuming A is true
-/

-- Case A true, B true
/-
At this point you really *have to see* 
that there is a contradiction in what we
have assumed, i.e., in our context. We've  
got a proof that neither A or B is true, but
we also have proofs that each of A and B is 
true. To finish this part of the proof, just
not that a and b, we can construct a proof 
of A ∧ B (by and.intro), yielding a direct
contradiction with h.
-/
let ab := and.intro a b,  -- ab proves A ∧ B
/-
The let construct is just another way to bind
a name to a value in the local context. Note
that ab gets added to your context.
-/

/-
Whenever you have a direct contradiction, in
the form of a proof of ¬X and a proof of X in
your assumptions/context, you can combine them
to derive a proof of false, by "applying" the 
proof of ¬X (i.e., X → false) to the proof of 
X, to derive a proof of false. A proof of false
is an impossibility, which means that the case
in question can't actually ever happen, so you
are done with having to think about it. That is
what false elimination does for you: you can 
now ignore the current goal and be done. 
-/
let f := (h ab),
apply false.elim f,
/-
Lean can automate the previous two steps in
cases where you have a contradiction in your
context. To see that work, comment out the
previous two lines and uncomment the next one.
-/
-- contradiction,



-- Now we turn to the second case: A true, B false
/-
Look at the goal: a proof of a disjunction.
Now look at your context. You have a proof 
(assumed in this case) of the right hand 
side. A simple application of or intro on
the right finishes the proof of this case
(lemma).
-/
apply or.inr nb,

/-
Now we address the two cases with 
A false, and B either true or false.
Before you read the next sentence look
hard to make sure you see how to to
prove it! A simple or introduction 
again does the trick.
-/
apply or.inl na,

/-
We have now proven the major lemma, 
that the implication is true in the
forward direction. That fills in the
first hole in our proof. Now we have
to construct a proof to fill the second
hole.
-/


-- REVERSE (You should add the comments here!)

-- B true
assume h,
cases h with na nb,
assume ab,
let a := and.elim_left ab,
contradiction,
-- apply na (and.elim_left ab),

assume ab,
let b := and.elim_right ab,
contradiction,
end 

/-
From the comments we've give and the 
ones you added to explain the proof of
the implication in the reverse direction,
you should be able to write a precise and
complete English language proof.
-/



/-
We now state and partially prove the second
DeMorgan law. We prove it in one direction,
leaving the proof in the reverse direction as
an exercise. You should also comment the whole
formal proof as a step towards having a full
English language proof.
-/

example : ∀ (P Q : Prop), ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
begin
assume P Q,
apply iff.intro _ _,


-- FORWARD

assume h,
apply or.elim (classical.em P),

-- Case P true
assume p,
let porq : P ∨ Q := or.inl p, -- new
contradiction,

-- Case P false
assume np,

apply or.elim (classical.em Q),

assume q,
let porq : P ∨ Q := or.inr q,
contradiction,

/-
You should be able to finish
this proof by yourself without
much difficulty at all.
-/


end 