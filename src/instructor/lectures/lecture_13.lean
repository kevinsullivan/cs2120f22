/-
UPDATE: Test distributed after class on 
Monday. Monday will be a review day. The
test is due back Wednesday before class.
In class Wednesday we will have at least
a short quiz to sanity check what you will
have submitted for the test. We reserve the
right to do follow-on in-person testing if
the results indicate a possible problem.
-/

/-
REVIEW: Last time we focused on the question, 
how do we construct a proof of ∃ x, P x.  

To do so, you apply the introduction rule for
exists. It's called exists.intro in Lean. You
apply it to two arguments: a specific value, w,
in place of x, and a proof that that particular
w satisfies the predicate, P, i.e., that there 
is a proof of the proposition, P w. 

In other words, you can think of a proof of
∃ x, P x, as a pair, ⟨w, pf ⟩, where w is a
witness and pf is a proof of P w.
-/

/-
Today we'll delve deeper into the mysteries
of exists elimination, or how you can *use*
a proof of ∃ x, P x.

Here's the idea: If you have a proof, ex, of
of ∃ (x : X), P x, you can apply exists.elim
to ex, and (after a few more simple maneuvers)
have yourself a specific value, (w : X), and 
a proof that w satisfies P, i.e., (pf : P w). 
The idea is that you can then uses the values
in your subsequent proof steps.

Why does this rule make sense? Consider a very
simple example. If I tell you there exists some
green ball, you can say, "well, call it b," and
give that we know it's green, we also know that
it satisfies the isGreen _ predicate, so we can
also assume we have a proof of (isGreen b). In
this example, b is a witness to the fact that
some object satisfies the predicate. The proof
then shows for sure that that is so.
-/

/-
There is (exists) a Boolean value, b, that 
satisfies the predicate, b && tt = f.
-/
example : ∃ (b : bool), b && tt = ff :=
begin
  apply exists.intro ff,  -- apply intro to witness
  exact rfl,              -- leaving proof as a subgoal
end

/-
If there's a Boolean value that satisfies
that predicate, then there's a Boolean value.
-/
example : 
  (exists (b : bool), b && tt = ff) → 
  (∃ (b : bool), true) :=
begin
 assume h,              -- assume premise
 cases h with w pf,     -- eliminate exists
 apply exists.intro w,  -- introduce exists
 trivial,               -- the rest is easy
end


/-
Let's set up some assumptions so that 
we can explore their consequences when
it comes to existentially quantified
propositions.
-/

/-
Beachballs! What could be more fun
-/

axioms 
  (Ball : Type)           -- There are balls
  (Green : Ball → Prop)   -- a Ball can be Green
  (Red : Ball → Prop)     -- a Ball can be Red 
  (b1 b2 : Ball)          -- b1 and b2 are balls
  (b1r : Red b1)          -- b1 is red
  (b1g : Green b1)        -- b1 is green
  (b2r : Red b2)          -- b2 is red


/-
Translate the propositions into English, then
prove them formally.

If there's a Ball that's Red and Green then 
there is a ball that's Red.
-/
example : 
  (∃ (b : Ball), Red b ∧ Green b) → 
  (∃ (b : Ball), Red b) :=
begin
  assume h,               -- assume there's a red and green ball
  cases h with b rg,      -- get a name, b, for the ball and a proof about b
  apply exists.intro b,   -- use b as a witness to the proposition to be proved
  exact rg.left,          -- the proof it's red is part of that it's red and green
end 

/-
If there's a ball, b, that's red or green
then there's a ball, b, that greed or red.

-/
example : 
  (∃ (b : Ball), Red b ∨ Green b) → 
  (∃ (b : Ball), Green b ∨ Red b) :=
begin
  assume h,             -- there's ball that's red or green
  cases h with w pf,    -- name it w with pf a proof of Red w ∨ Green w
  apply exists.intro w, -- use w as witness, need proof of Green w ∨ Red d
  cases pf,             -- basically proof of X ∨ Y → Y ∨ X at this point
  exact or.inr pf,
  exact or.inl pf,
end 

/-
How about this one? Translate it into Enlish. Do
you believe it?
-/
example : 
  (∃ (b : Ball), Red b ∨ Green b) → 
  (∃ (b : Ball), Red b) :=
begin
  assume h,
  cases h with w pf,
  cases pf, 
  apply exists.intro w,
  assumption,
  apply exists.intro w,
  _
end 

/-
If there's a red ball then there's a ball that's red or green.
-/
example : -- be sure you can do this one yourself!
    (∃ (b : Ball), Red b) → 
    (∃ (b : Ball), Red b ∨ Green b) := 
begin
end 

/-
Social Networks
-/

axioms
  (Person : Type)
  (Nice : Person → Prop)
  (Likes : Person → Person → Prop)

/-
What does this say, in English? It is true?
-/
example : 
  -- If there's a person, p1, who everyone likes,
  (∃ (p1 : Person), ∀ (p2 : Person), Likes p2 p1) → 
  -- then everyone likes someone
  (∀ (e : Person), ∃ (s : Person), Likes e s) :=
begin
  assume h,
  cases h with p pf,
  assume e,
  apply exists.intro p,
  exact (pf e),
end

/-
Write formal expressions for each of the following
English language sentences.
-/

-- Everyone likes him or herself

-- Someone doesn't like him or herself

-- There is someone likes someone else

-- No one likes anyone who dislikes them

-- Everyone likes anyone who is nice

-- No one likes anyone who is not nice

/-
If everyone who's nice likes someone, then
there is someone whom everyone who is nice 
likes. (Is this true or not.)
-/