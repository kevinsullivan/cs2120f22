import data.set

/- 
PART II: BASIC SET THEORY

Give formal and English language proofs of 
the following conjectures.
-/

def evens : set ℕ := { n | n%2 = 0}

example : ({ 0, 2 } : set ℕ) ⊆ evens :=
/-
Before looking at the proof script, spend
a good bit of time trying to be sure that
you see how the proof will work. We want
to prove a subset relation, so we want to
prove that for all values, v, if v is in
the first set, then v is in the second. 
The rest of the proof is by case analysis.
v ∈ {0, 2} means v = 0 ∨ v = 2. These are
the cases. In each case, we need to show
that the value, v, is in the second set. 
This means that the value satisfies the
set membership predicate, so we will need
to prove (evens 0) and (evens 2). Writing
out the definition of evens, we'll need to
prove 0 % 2 = 0 and 2 % 2 = 0, and these
are true by the reflexivity of equality.

Here we hope wou see how vitally important 
it is to *learn* the basic definitions and
to *look them up* again if you forget them 
or get stuck. Always go to the definitions
if you get stuck. That's how to learn or to
*remember* what the symbols and other terms
mean. Put all the smaller pieces together
again, and often that will show you how to
get unstuck. 

This principle is particularly important
right now because we've introduced a major
new layer of abstractions, from logic to 
set theory, and associated new notations
by which to refer to these new concepts.
You need to *memorize* the definitions of
basic set notations to be able to write 
propositions and produce proofs in set
theory.
-/

/-
So here's a proof script in Lean. Use it
to 
-/

begin
  /-
  Uncomment next line to see how to use show
  to rewrite a goal to "definitionally equal" 
  form. The rewriting here makes it easier to
  see exactly when the first two moves are to
  assume that you're given argument values, n
  and h. This rewriting is not needed though 
  for the rest of the proof to work as is.
  -/
  show ∀ n, n = 0 ∨ n = 2 → n ∈ evens,
  assume n,
  assume h,
  cases h,

  -- case: n = 0
  rw h,
  /-
  Uncomment the following lines if you want
  to see in more detail why it makes sense 
  that rfl is what's needed to finish the
  proof. (But before you do, try to work it
  out in your own head!)
  -/
  -- unfold evens,
  -- show {n : ℕ | n % 2 = 0} 0,
  -- show 0 % 2 = 0,
  exact rfl,

  -- case: n = 2
  cases h,
  /-
  At this point you have h, a proof of 2 = 2,
  (albeit written in a strange way by Lean),
  and you need to prove that 2 (writen weirdly)
  is in the evens set. In this case, the h is
  not needed, as the proof that "2 is even" is
  trivial [ok, it's by reflexivity of equality]
  -/

  --uncomment for unnecessary gory details!
  /-
  show 2 ∈ evens,
  show evens 2,
  unfold evens,
  show 2 % 2 = 0,
  show 0 = 0,
  -/
  exact rfl,    -- Ta Da!
end


/-
We now look at the concept of *equality* 
of sets. To show that two sets are equal,
e.g., L = X, we need to show that a value
is in L if and only if it's in X. This is
the same as showing L ⊆ X ∧ X ⊆ L. This
in turn means 
  ∀ x, 
    (x ∈ L → x ∈ X) ∧
    (x ∈ X → x ∈ L)
which we can also write as
  ∀ x, x ∈ L ↔ x ∈ X.
Now to get from a proof of that to a proof
of L = X requires a new axiom, the axiom 
of set extensionality. It just says that 
if we prove ∀ x, x ∈ L ↔ x ∈ X then we 
can, by applying the axiom, deduce that
L = X. The set extensionality axiom in 
Lean is called ext, defined in the set
namespace; so you can refer to it either
as set.ext, or you can open the set
namepace and then just call it ext. 
-/
#check @set.ext 

/-
Remember that you can think about an
implication, P → Q, in two ways: first
(reading left to right), if P then Q; 
second (reading right to left), to show
Q it will suffice to show P. Reading #2
is what we want here. The salient point
is that if you know P → Q and you need
to show Q, then it will suffice to show
P. P → Q thus allows you to reduce the
problem of showing Q to the problem of
showing P. This is the principle that 
we use in this next concrete example.

To prove L = X, it will suffice to prove 
∀ x, x ∈ L ↔ x ∈ X. If one has a proof
of ∀ x, x ∈ L ↔ x ∈ X, then one easily
obtains a proof of L = X by applying the
axiom of extensionality. Therefore (now
go right to left), if we need to prove
L = X, then it will suffice to have a
proof of ∀ x, x ∈ L ↔ x ∈ X, as one 
then just applies ext to get a proof of
X = L. 

Now look again at the definition of ext.

  set.ext : 
    ∀ {α : Type u_1} {a b : set α}, 
    (∀ (x : α), x ∈ a ↔ x ∈ b) → a = b

What is says is that we can apply ext 
such a proof to derive a proof of L = X.

Here's the most important point: If we 
apply ext to a hole where the proof of
the bi-implication should be, we will 
have our proof of L = X with only the
bi-implication proof remaining to be
produced. In this sense, applying the
axiom of set extensionality *without*
giving a proof of the bi-implication,
*reduces* the problem of proving L = X
to the problem of proving ∀ x, x ∈ L ↔ 
x ∈ X. And that is what we see next. 
-/

example : ∀ {α : Type} (L X : set α), L ⊆ X → ((L ∩ X) = L) := 
begin
  intros α L X h,
  apply set.ext _,  -- reduce = to ↔ by set extensionality
  /- 
  That's the whole proof as long as we can fill in the _
  That's what the rest of this proof script then does. 
  Notice again how "applying an implication theorem" 
  can be used to reduce a current proof goal to goals 
  the satisfaction of which "will suffice" to enable
  construction of the proof that's needed.
  -/
  assume x,
  split,
  -- forward
  assume h,
  /- 
  Remember, h is a proof of a conjunction
  so "cases h" really does and elimination 
  giving us the left and right subproofs as
  the arguments that must have been given as
  arguments to the and.intro that must have
  been used to construct such a proof in 
  the first place.
  -/
  cases h with l r,
  exact l,
  -- quiz: would "exact h.left" have worked?
  -- predict the answer before checking

  -- backward
  assume k,
  exact and.intro k (h k),
  /-
  So this last "proof move" will take a little
  time to think about. Look at the goal and think
  for yourself what you really need to prove here.
  Go back to the definitions! x ∈ L ∩ X really 
  just means L x ∧ X x. Does this help you to see
  why and.intro is required here, and what each 
  of the terms in the preceding express means?
  -/
end 

