import tactic.ring
import tactic.norm_num

/- #1 Formalizing propositions in English 

Translate the following English statements 
into formal propositions. We give an example
first. The prove the proposion formally. 
Finally write an English language proof.
-/

/- 
For any natural number, n, if n ≠ 0, then there
is another natural number, call it n', such that 
n is the successor of n' (n = nat.succ n'). You
should see that n' will have to be one less than n.
-/

def p1a : Prop := 
  ∀ (n : ℕ),            -- For any natural number n
    n ≠ 0 →             -- If n ≠ 0 then
    ∃ (n' : ℕ),         -- there is some number n'
      n = nat.succ n'   -- such than n is one more than n'

/-
The proof is by case analysis on n. What you 
need to know, again, is that there are only 
two possible cases for a natural number, n. It
is either 0 or the successor of another number,
let's call it n'.

The first case contradicts our assumption that
n = 0, and so can be dismissed. In the second
case, there's only one value for n' that will
satisfy the predicate, so give it as a witness
to the ∃ then prove it satisfies the predicate.
Note that Lean will use the notation, n.succ, 
as a shorthand for nat.succ n. 
-/
example : p1a :=        -- We are to prove p1a
begin

-- By the definition of p1a
unfold p1a,            

-- We are to 
show ∀ (n : ℕ), n ≠ 0 → (∃ (n' : ℕ), n = n' + 1),

-- To start let n be an arbitrary nat and assume n ≠ 0
assume n h,

-- It remains for us to ...
show ∃ (n' : ℕ), n = n' + 1,


-- solve for n' : n + 1 = n' + 1


/-
The remaining proof is by case analysis
on n. The cases (by the definition of nat,
which we are about to see) are n = 0 and 
n is the successor of a one-smaller number, 
n'. 
-/
cases n with x,

/- In the first case, we replace n with 0,
reducing h to 0 ≠ 0, which is a contradiction.
-/
contradiction,

-- In the second case, we need to ...
show ∃ (n' : ℕ), x.succ = n' + 1,

/-
Work hard to understand this goal. It requires
that we show that there exists a number n' such
that n'+1 = n = succ x. In other words, we need 
n' such that n' + 1 = n = x + 1. It should now be 
clear: x satisfies this equation, so we can use 
it as the witness to prove the existential 
proposition that remains to be proved. 
-/
apply exists.intro x _, 

/- 
All that now remains to prove is the equality
(yielding the second argument to exists.intro).
-/
apply rfl,
end

/-
-/

/- #1A.
State and prove the proposition that there's some
natural number whose square is 144.
-/

-- Pick n=12 then show 144 = 12*12, by arithmetic
example : ∃ n, n*n = 144 := 
begin 
apply exists.intro 12,
exact rfl,
end 

/- #1B.
State and prove the proposition that there is 
some string, s, such that s ++ "!" is the string, 
"I love logic!." Note: In Lean, ++ is notation
for string.append, the function for gluing two
strings together into one.
-/

-- Proof strategy is same as previous problem
example : ∃ s, s ++ "!" = "I love logic!" :=
  exists.intro "I love logic" rfl

-- Extra examples

example : ∃ s : string, s.length = 5 := 
exists.intro "Lean!" rfl

example : ∃ n, n*n + 5 = 30 := exists.intro 5 rfl
  
example : ∃ n : int, n*n = 1 := exists.intro 1 rfl

/-
There's an important lesson here: When you have
to prove an ∃ proposition, you have to *search*
for and come up with a witness that satisfies the
given predicate. In general, this can be hard. 
It often involves doing a bunch of math and/or
other reasoning "on the side." Here for example,
you have to "search for" a string that satisfies
the predicate. It's easy in this case but often 
isn't so trivial. The important point is that to
prove an ∃ proposition often involves solving a
problem, such as a set of equations, to find a
witness that will "work."
-/

example : ∃ n, n*n - 1 = 0 := exists.intro 1 rfl 

/- #1C.

Formally state and prove the proposition that
there are three natural numbers, x, y, and z, 
such that x*x + y*y = z*z. Hint: exists.intro
takes just one witness as a time, so you will
have to apply it more than once.
-/

-- example : ∃ (x y z : nat), x*x + y*y = z*z :=
example : ∃ x : ℕ, ∃ y, ∃ z, x*x + y*y = z*z :=
begin
/-
The key, simple, insight that unlocks a proof
of this theorem is to know that ∃ (x y z), ...
means ∃ (x), ∃ (y), ∃ (z), ... You thus need 
to give a witness for x, then prove the rest,
which means giving a witness for y then proving
the rest, which means giving a witness for z
then proving the rest, which is finally done
by arithmetical simplification and reflexivity
of equality.
-/
apply exists.intro 3 _,
apply exists.intro 4 _,
apply exists.intro 5 _,
exact rfl,
end

/- #1D
Define a predicate called pythag_triple taking
three natural number arguments, x, y, and z,
yielding the proposition that x*x + y*y = z*z.
-/

def pythag_triple (x y z : ℕ) : Prop := x*x + y*y = z*z

#check pythag_triple 1 2 3
#reduce pythag_triple 3 4 5

/- #1E
State the proposition that there exist x, y, z, 
natural numbers, that satisfy the pythag_triple, 
predicate, then prove it. (Use "example : ...")
-/

-- Know how to use predicates to form propositions!
example : ∃ (x y z), pythag_triple x y z :=
begin
/-
The rest is d simple application of #1C.
-/
apply exists.intro 3,
apply exists.intro 4,
apply exists.intro 5,
-- unfold pythag_triple, -- not necessary
-- show 25 = 25,
exact rfl,
end

example : ∃ (x y z), z ≠ 5 ∧ pythag_triple x y z :=
begin
apply exists.intro 5,
apply exists.intro 12,
apply exists.intro 13,
unfold pythag_triple,
apply and.intro _ _,
-- prove 13 ≠ 5 by negation
{ 
  show ¬ 13 = 5,
  show 13 = 5 → false,
  assume h,
  cases h, 
},
-- prove the remaining equality proposition
{
  exact rfl,
}
end

-- REVIEW 12/7 stopped here

/- #2A

Define a predicate, (multiple_of n m), true
if and only if n is a multiple of m. Hint: 
What has to be true for this to be the case?
-/

def multiple_of (n m : ℕ) := ∃ (k), n = m * k  

/- #2B

Using the predicate, multiple_of, state and 
prove the proposition that every natural number 
that is a multiple of 6 is also a multiple of 
3. Hint: you can use "unfold multiple_of at h,"
to expand the definition of multiple_of in the
hypothesis, h (assuming you call it that).

Hint: Put the argument you will give to exists
intro in parentheses (needed for correct syntax).

Hint: You might end up with n = 3 * (2 * w) 
as a goal. The "ring" tactic in Lean will 
simplify this expression to n = 6 * w. 

Before you do the work, let's talk a little
more about the "ring" tactic. First, where does
the name come from? Second, what does it do?

A "ring" in college-level algebra (and beyond)
is any set of values (such as natural numbers) 
with + and * operations that satisfy the usual 
rules of arithmetic (such as the distributive
laws, the associativity of + and *, etc). Not
only the natural numbers form a ring, but so
do polynomials, and many other kinds of math
objects as well.

The ring tactic is used to put any expression 
involing any ring" into a "normal" form. What 
"normal" means in this context is that if you 
put two mathematically equivalent but different 
expressions in normal form, then you get the 
same "normalized" expression in both cases,
making it easy to compare them for equality. 

So, in particular, if you want to know whether 
a+(b+c)=(a+b)+c, with these "ring" expressions
on both sides of the = sign, put both expresions
in normal form and see if they are equal (which 
again they are if + is addition in any "ring").

A good English translation of the use of the 
ring tactic is "by basic algebra."

Here's an example. Is ℕ addition associative? 
-/

example (n m k : ℕ) : n + (m + k) = (n + k) + m := 
begin 
ring 
end  

/-
Whoa! It's that easy to prove addition 
associative? Yep, "by simple algebra." Thankfully 
someone else has written this beautiful tactic so
you don't have to do all the algebra yourself.
-/

/-
As a small aside on Lean syntax, if a tactic script is 
just one tactic long, you can use "by <tactic>" instead 
wrapping the tactic in a begin-end block.
-/
example (n m k : ℕ) : n + (m + k) = (n + k) + m := by ring

/-
Ok, with that background in place, let's return to the
problem we were discussing. Is it true that if any natural
number if a multiple of 6 then it's also a multiple of 3?

Before you even consider writing a proof, whether in Lean
or in English, figure out yourself whether the proposition
appears true or not. Try to prove it "mentally" first. 

The key question here is, what does it even mean for a 
number, n, to be a multiple of 6. Well, n is a multiple
of 6 if there's some number, say k, such that n = k * 6,
right? Now you should be able to formally write, and then
prove, the proposition on the table. Is it true that for
any n, if n is a multiple of 6 then it's a multiple of 3? 
Why, exactly? Well, there would have to be another number
that makes n when you multiply it by 3. The trick here is
to figure out what that number has to be so you can prove
that there does exist such a number.
-/

/-
We want to prove the proposition that if any n is a
multiple of 6 then it's also a multiple of 3. You are
now expected to understand how to write propositions 
that use predicates that you yourselves have defined,
and of course to translate "every" and "if ... then"
into predicate logic.
-/
example : ∀ (n), multiple_of n 6 → multiple_of n 3 :=
begin
-- Assume n is arbitrary
intros n,

-- Assume in addition that it's a multiple of 6
assume h,

-- Unfold the definition of multiple_of in h for clarity
unfold multiple_of at h,

-- From h deduce that there's some w such that n = 6 * w
cases h with w pf,

-- By the definition of multiple_of we are to ...
unfold multiple_of,  

-- Show
show ∃ (k : ℕ), n = 3 * k,

/-
Now the lesson about having to search
or solve for an appropriate witness is
the key! Given what you have to work with,
what number will satsfy the predicate of 
the remaining existentially quantified 
goal? Well if n = 6 * w and we want to
show that n = 3 * w' (where w' will be
our witness for the remaining proof), 
what does w' have to be? You have to 
solve a simple set of equations here 
to answer the question. 

n = 6 * w
  = (3 * 2) * w
  = 3 * (2 * w)
  = 3 * w' where w' = 2 * w
That's it!
-/
apply exists.intro (2*w) _, -- figure out what witness to give! 

/-
We have a proof that n = 6 * w and we need
to show that n = 3 * (2 * w). Formally speaking
3 * (2 * w) = (3 * 2) * w by the associativity
of multiplication, which then reduces to 6 * w,
and we already have a proof that n = 6 * w. We
can avoid having to explicitly apply low-level
arithemtical axioms and theorems by using the
"ring" tactic in Lean, as explained above. In
English, again, you can just say, "then by basic 
arithmetic, n = 6 * w."
-/
ring, 

/-
Which is proved by the fact that it's already
an assumption that n is a multiple of 6.
-/
assumption,               -- and done. QED.
end 


/- #2C.

Is it true that if n is a multiple of h, and h
is a multiple of k, that n is a multiple of k? 
Formally state and then prove the proposition.

In writing this proof, you might need to use one
of the two fundamental axioms of equality, via 
the "rewrite" tactic (abbreviated rw). Here again
is how it works:

If you've already proved/know, and so have in 
your context, a proof of an equality, such as 
h : m = k, and if  m appears in your goal, then
you can replace the m with k by using "rw h". 
The rewriting of m to k in your goal is justified
by the fact, pf, that m = k. 

The rw tactic is applying the second axiom of 
equality, which states that if m = k and you 
have a proof, h : P m, for some predicate P,
then you can conclude that P k is true, too. 

In other words, "you can substitute equal terms 
for each other, and that is valid."

Similarly, if you have h : m = k and a goal with
*k* in it, you can rewrite the k to m using 
rw <- h. The left pointing arrow indicates you
want to use the equality right to left rather
than left to right. 

With all that in mind, here we go.
-/


-- Write the proposition involving your own predicates
example (n h k) : multiple_of n h → multiple_of h k → multiple_of n k :=
begin
-- We've already assumed that n h and k are arbitrary natural numbers
-- Now assume n is a multiple of h and h is a multiple of k.
assume monh mohk,

-- What remains is to ...
show multiple_of n k,

/-
From the fact n is a multiple of h we 
can deduce that there's some natural 
number, a witness to this fact, let's
call it w_nh, along with a proof that
it is a witness.
-/
cases monh with w_nh pf_nh,

/-
Similarly, we deduce a witness, w_hk, 
to the fact that h is a multiple of k,
with a corresponding proof. 
-/
cases mohk with w_hk pf_hk,

/-
Now you're at the point where you have
to do some algebra to figure out what 
witness will work to prove the conclusion
of the conjecture (the proposition to be
proved).

From n = h * w_nh and h = k * w _hk we
deduce n = (k * w_hk) * w_nh. Then we can
see tgat by associativity of multiplication
this equals k * (w_hk * w_nh), so n is a 
multiple of k, with witness w_hk * w_nh.
-/
apply exists.intro (w_nh * w_hk),

-- We can now expand the definition of n
rw pf_nh,

-- Then expand the definition of h
rw pf_hk,

/-
And finally "normalize" both sides, of
the equation (which in this case involves
applying associativity of multiplication)
to show that both sides are equal. I.e.,
"Finally, by simple arithmetic QED." 
-/
ring,
end

/-
Next is practice with exists.elimination
-/

/- #3A

Formally state and prove that if everyone 
who knows logic is cool and someone knows 
logic, then someone is cool. 

Once again the trick in proving an exists
(the conclusion of the implication) is to
"figure out" what/who to use as a witness.

In this case, before you even think about
using Lean, just think about what the logic
says. 

Someone knows logic. The principle of exists
elimination says you can give that person a 
name, e.g., w, and have a proof that w knows
logic. Furthermore, you can assume everyone
who knows logic is cool. *So you know at least
one person who must be cool* Who is it? Once
you answer this question, the proof, whether
in English or in Lean, is easy.
-/

/-
There are several ways to write the proposition
formally. In this solution, we introduce all of
the assumptions as arguments (before the colon),
implicitly creating the context in which the 
rest of the proof is to be given.
-/

example 
  -- Represent people as objects of a type, Person
  (Person : Type)

  -- Represent "knows logic" as a predicate on people
  (KnowsLogic : Person → Prop)

  -- Similarly represent "is cool" as a predicate on people
  (isCool : Person → Prop)

  -- Formalize the idea that if anyone knows logic they are cool
  (LogicMakesCool : ∀ (p), KnowsLogic p → isCool p)

  -- Formalize the idea that someone knows logic
  (SomeoneKnowsLogic : ∃ (p), KnowsLogic p) : -- here's the colon!
  -- In this context show that there's someone who is cool
  ∃ (p), isCool p :=      
begin 
  -- Someone knows logic, so give that person a name, w, and get a proof w knows logic
  cases SomeoneKnowsLogic with w pf,
  
  -- Now 
  show ∃ (p : Person), isCool p,

  -- We know at least one person who must be cool
  apply exists.intro w _,

/- 
Finally since anyone who knows logic
is cool, and w knows logic, w must be
cool, by universal specialization (∀
elimination). 
-/
  apply LogicMakesCool w pf,
end



/- #3B
Formally state and prove the proposition that if
someone is not happy then not everyone is happy.
-/

example 
  -- Let's talk about people
  (Person : Type)
  -- And that people can be happy
  (Happy : Person → Prop) :
  /-
  In this context, show that if there is
  someone who is unhappy (there must now
  be at least one!) then it's not true 
  that everyone is happy.
  -/
  (∃ (p), ¬(Happy p)) →
  (¬ (∀ (p), Happy p)) 
  :=
begin
  -- Start by assuming that someone is not happy
  intros h,

  -- By exists elim given them a name, w, and get of proof of their unhappiness
  cases h with w w_unhappy,

  -- The rest is a proof by negation. Assume that everyone *is* happy
  assume everyone_happy,

  -- Derive a proof that w is happy
  let w_happy := everyone_happy w,

  -- But that contradicts 
  contradiction,
end


/- #3C
Formally state and prove that stating that
everyone  is happy is equivalent to saying 
that no one is unhappy. 

Hint: In one direction, you might need 
to use classical reasoning; and remember
you can get a proposition (on which to do
classical case anaysis) by applying a
predicate to the right arguments. And
a final hint: Sometimes you have to use
information you have to prove something 
you don't yet have in order to make it
clear that there's a contradiction in
your set of assumptions. 
-/
example 
  (Person : Type)
  (Happy : Person → Prop) :
  /-
  Now prove this equivalence. Do us parens
  around the two sides of the biconditional.
  It never hurts logically to add parens to
  be sure you're not writing a proposition
  other than the one you mean to prove.
  -/
  (∀ (a), Happy a) ↔ (¬ ∃ (a), ¬ Happy a) :=
begin

  /- 
  By iff introduction it will suffice to prove
  the implication in each direction. We now do
  that.
  -/
apply iff.intro,

  -- Forward direction
  
  -- Assume everyone's happy
  assume everyone_happy,

  -- By negation: assume someone's unhappy and ...
  assume someone_unhappy,

  -- Prove that that's a contradiction
  show false,

  -- Someone's unhappy! Call them w and get a proof they're unhappy. 
  cases someone_unhappy with w w_unhappy,

  -- Apply "everyone's happy" to w to prove w's happy
  apply w_unhappy (everyone_happy w),

  -- And that's a contradiction

  -- Backward direction

  -- Assume no one is unhappy, then ...
  assume noone_unhappy,

  -- Show that everyone is happy
  show ∀ (a : Person), Happy a,

  -- Let p be an arbitrary person, and ...
  assume p,

  -- Show that p is happy

  /-
  Now you're stuck. Or are you?
  Constructively yes, classically no!
  Assume a person can only be happy or
  not happy!
  -/
  cases (classical.em (Happy p)) with p_happy p_unhappy,

  -- Case #1: P is happy. By assumption.
  assumption,

  -- Case #2: P is unhappy.

  /-
  The trick here is to see that you have a proof
  that p is unhappy and you also have a proof that
  there's no one who's unhappy. There has to be a
  contradiction there! All you need to do now is
  to use the fact that p is unhappy to prove that
  someone is unhappy. That make the contradiction
  explicit.
  -/

  let someone_unhappy := (exists.intro p p_unhappy),
  /-
  Sometimes you get a funny looking definition
  at this point, but the key observation (please
  look carefully!) is that you have a proof that 
  someone is unhappy and you have a proof that no
  one is unhappy. That's a contradiction. QED.
  -/
  contradiction,
end 



/- #3D

Formall state and prove the proposition
that if there doesn't exist an object of
some type T with some property, P, then
any object of that type has the property
¬P. Hint: Again we represent a "property" 
of objects of a certain type as a predicate
taking objects of that type.
-/
example 
  (T : Type)
  (P : T → Prop) :
  (¬∃ (x), P x) → 
  ∀ (x), ¬(P x) :=
begin
-- assume there;s no x with property p
intros h,
-- let x be an arbitrary value
assume x,
-- by negation: assume P x, show contradiction
assume px,
show false,
-- from x and Px show ∃ x, P x
let ex_x_Px := exists.intro x px,
-- that's a direct contradiction
-- therefore ∀ x, ¬P x 
contradiction,
end


/- #3D
Formally state and prove that if there's 
an object with the property of "having 
property P or property Q" then there's 
an object with property P or there's an 
object with property with property Q.
Remaining exercise: fill in English 
comments for each step in the formal 
proof then string them together with 
appropriate language to render a great
natural language proof.
-/

example 
  (α : Type)
  (P : α → Prop)
  (Q : α → Prop): 
  (∃ (x), ((P x) ∨ (Q x))) → 
  (∃ (x), P x) ∨ (∃ (x), Q x) :=
begin
-- You: Comment script; extract natural language proof.
assume h,
cases h with w pworqw,
cases pworqw with pw qw,
left,
exact (exists.intro w pw),
right,   
exact (exists.intro w qw),
end

