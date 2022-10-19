/-
CS 2120 F22 Homework #4. Due Oct 13.
-/

/- #1A [10 points]

Write a formal proposition stating that 
logical and (∧) is associative. That is, 
for arbitrary propositions, P, Q, and R,
P ∧ (Q ∧ R) is true *iff* (P ∧ Q) ∧ R is, 
too. Replace the placeholder (_) with your
answer.
-/

def and_associative : Prop := 
  ∀ (P Q R : Prop), 
    (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) 


/- #1B [10 points]

Give an English language proof. Identify
the inference rules of predicate logic
that you use in your reasoning.
-/

/-
Answer: 
-/

/- #1C [5 points]

Give a formal proof of the proposition.
Hint: unfold and_associative to start.
-/

theorem and_assoc_true : and_associative :=
begin
unfold and_associative,
assume P Q R,
apply iff.intro _ _,

-- forward
assume h,

/-
let pq : P ∧ Q := and.elim_left h,
let r : R := and.elim_right h,
let p : P := and.elim_left pq,
let q : Q := and.elim_right pq,
-/

cases h with pq r,
cases pq with p q,

/-
apply and.intro _ _,
cases h with pq r,
cases pq with p q,
exact p,
apply and.intro _ _,
exact and.elim_right(and.elim_left h),
exact (and.elim_right h),
-/

/-
cases h with pq r,
cases pq with p q,
-/
apply and.intro p (and.intro q r),

-- Reverse
assume h,
cases h with p qr,
cases qr with q r,
exact (and.intro (and.intro p q) r),
end




/- #2A [10 points]

Write the proposition that ∨ is associative.,
analogous to the proposition about ∧ in #1.
-/

def or_associative : Prop := 
  ∀ (P Q R : Prop), P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R


/- #2B [10 points]

Write an English language proof of it, citing
the specific inference rules you use in your
reasoning.
-/


/- #2C [5 points]

Complete the following formal proof.
-/

theorem or_associative_true : or_associative :=
begin
unfold or_associative,
assume P Q R,


apply iff.intro _ _,

-- forward
assume h,
apply or.elim h _ _,

-- case P
assume p,
apply or.inl _,
exact (or.inl p), 

-- case Q or R
assume qr,
apply or.elim qr _ _,

-- case Q
assume q,
apply or.inl _,
exact (or.inr q),

-- case R
assume r,
apply or.inr r,

-- reverse
 
-- TO DO

end


/- #3A [10 points]
Write a formal statement of the proposition.
-/

def arrow_transitive : Prop :=
  ∀ (P Q R : Prop), (P → Q) → (Q → R) → (P → R)


/- #3B [10 points]

Write an English language proof of the proposition
that for any propositions, X, Y, and X, it's the
case that (X → Y) → (Y → Z) → (X → Z). In other
words, implication is "transitive." Hint: Recall
that if you have a proof of, say, X → Y, and you 
have a proof of X, you can derive a proof of Y by
arrow elimination. Think of it as applying a proof
of an implication to a proof of its premise to get
yourself a proof of its conclusion.
-/


/- #3C [5 points]. 
Write a formal proof of it.
-/

example : arrow_transitive :=
begin
  unfold arrow_transitive,
  assume P Q R,
  assume pq : P → Q,
  assume qr : Q → R,
  assume p : P,
  let q : Q := (pq p),
  let r : R := (qr q),
  -- assumption,
  -- apply r,
  exact r,
end 


/- #4
Suppose that if it's raining then the streets
are wet. This problem requires you to prove that
if the streets are not wet then it's not raining.
-/

/- #4A [10 points]

Start by writing the proposition in predicate
logic by completing the following answer.
-/

def contrapositive : Prop :=
  ∀ (Raining Wet : Prop), 
    (Raining → Wet) → (¬Raining → ¬Wet)

/-
The proposition defined here isn't valid. It's
one of the classical fallacies, one that we saw
starting with propositional logic. Contrapositive
says if (R → W) → (¬W → ¬R). Consider a concrete
case: If whenever it rains R, the streets are wet
(W), then if the streets are not wet (¬W) then it
must not be raining (¬R).
-/

def contrapositive_corrected : Prop :=
  ∀ (Raining Wet : Prop), 
    (Raining → Wet) → (¬Wet → ¬Raining)

/- #4B [10 points]. 
-/

theorem contrapositive_valid : contrapositive_corrected :=
begin
unfold contrapositive_corrected,
assume R W h,
assume nw,
assume r,
let w := h r,
contradiction,
end

/- #4C [5 points]. 

Give an English language proof of it.
-/


/- #5. Extra credit.

Complete the following formal proof of the 
proposition that if for any proposition P, 
P ∨ ¬P is true, then for any propositions, 
X and Y, if it's not the case that X or Y
is true then it is the case that ¬X and ¬Y 
is true. 
-/

theorem demorgan1 : 
  (∀ (P : Prop), P ∨ ¬ P) → 
    ∀ (X Y : Prop), 
      ¬(X ∨ Y) → (¬X ∧ ¬Y) :=
begin
assume em X Y nxory,
cases (em X) with x nx,

-- case where X is true
let xory : X ∨ Y := or.inl x,
contradiction,

-- case where X is false
cases (em Y) with y ny,

  -- case where Y is true
let xory : X ∨ Y := or.inr y,
contradiction,

  -- case where Y is false
apply and.intro nx ny,

end

/- OPTIONAL, NOT NECESSARY FOR MIDTERM EXAM

A comment on or.intro_left and or.intro_right.
In Lean each of these takes two arguments: a
proof of the disjunct -- the proposition on 
one side of the ∨ -- that is to be proven true, 
*and* it takes as an argument the proposition 
that is not being proven true. In applications 
of these rules the proposition argument (not 
being proven) comes first, while the proof 
argument comes second.

The reason is that Lean needs to know what 
overall proposition is being proved. From the
proof argument it can infer the proposition 
being proved, but it needs the other proposition
as well to know the full (X ∨ Y) disjunction to
be proved. 

Here's an example:
-/

example : 0 = 0 ∨ 0 = 1 :=
begin
apply or.intro_left (0 = 1) rfl
/-
The "rfl" serves as a proof of 0=0.
But in addition, as the first argument
to or.intro, we need to provide the
*proposition* that is not being proved.
Here's that's (0 = 1). In contexts
where Lean can infer both disuncts,
you can use the simpler or.inl or 
or.inr, each of which just takes one
argument: a proof of the left or of 
the right side, respectively.
-/
end

