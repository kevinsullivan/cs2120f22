
import logic.relation

namespace hidden 

/- Equality (Relation)

We will now shift focus to the specific binary 
relation on any type, α, that we call equality.
Equality in Lean is polymorphic: Given any type
(in any type universe, from Sort 0, i.e., Prop,
all the way on up), we have a binary relation on
values of that type, of type α → α → Prop.
-/

#check @eq
-- eq : Π {α : Sort u_1}, α → α → Prop
-- infix ` = `:50 := eq

-- These expressions mean the same thing
#check eq 0 0
#check 0 = 0


#check eq 0
-- eq 0 : ℕ → Prop
-- a predicate: takes a value, yields an equality proposition 
-- "the property of a nat argument, n, being equal to zero"

/-
Beyond taking any type parameter, α, inferred implicitly
from the first explicit parameter, eq expects two explicit
parameters, one might call them a and b, both of type α. 
The result is the proposition that asserts that a = b. The
= sign is just an infix notation for eq.
-/

/-
Applying eq to the first, a, of its two arguments leaves 
one with a predicate that takes an argment, b, yielding the
proposition a = b.
-/

#check eq 0 0 -- a proposition, that 0 = 0
#check eq 0 1 -- a proposition, that 0 = 1

/-
Now you can make good sense of  the type of eq (=) in Lean. 
Applying "eq {α : Sort u} (a : α)" to a value, a, yields a 
predicate, (eq a), of type α → Prop. That is a predicate that
takes a second value, b, and yields the proposition (eq a b), 
also written as a = b.
-/

#reduce 0 = 0     -- usual notation
#reduce eq 0 0    -- representing this application expression
#reduce (eq 0) 0  -- remember: application is left associative
-- So that's what we mean when we write 0 = 0


/- PROOFS 

Up until now, all we've talked about is a mechanism
for generating propositions. What are the rules for 
constructing and using proofs of equality, and where
do they come from? 
-/

/-
Let's answer the first question first. Equality has
two inference rules: an introduction rule, eq.refl,
and an elimination rule, eq.subst. All other properties
of equality come from these two rules and the meaning
of "inductive definitions" in Lean (as we'll see in a
bit). 

The introduction rule establishes the fact (constructs
proofs) that every object of any given type is equal to
itself.
-/

#check @eq.refl
-- ∀ {α : Sort u} (a : α), eq a a

#check eq.refl 0
-- eq 0 0, i.e., proof of 0 = 0

example : 0 = 0 := eq.refl 0

-- When Lean can infer "a" you can use rfl.
example : 0 = 0 := rfl

#check @rfl

/-
Note: in our logic you can't form a proposition that 
two things of different types are equal. It's just a 
type error, given the definition of eq.
-/

#check tt = "hi"    -- type error


/- Elimination rule: substitutability of equals

The second axiom of equality defines its elimination 
rule: that is, how we can *use* a proof of an equality.
If you have a predicate, P : α → Prop, for some type, 
α, 
-/

#check @eq.subst
/- eq.subst : 
  ∀ {α : Sort u_1} 
  {P : α → Prop} 
  {a b : α}, 
  a = b →           -- if you know a = b
  P a →             -- and if you know P a
  P b               -- you can deduce P b
-- in reverse, 
-- to show P b 
-- suffices P a and a = b
-/

/-
What this rule really says is that if you 
have a goal, P b, and you know a = b, you
can rewrite the goal as P a and the result
will be equivalent.

The following example sets up the use of 
eq.subst. There are balls, balls can be 
blue, a and b are balls, a is b, and a is
blue. The goal is to show that b is Blue.
That is done by applying eq.subst to the
proof of equality of a and b, and to the
proof that a is Blue. 
-/

example 
  (Ball : Type)
  (Blue : Ball → Prop)
  (a b : Ball)
  (eq_balls : a = b)
  (a_is_Blue : Blue a) :
  Blue b := 
eq.subst eq_balls a_is_Blue

/-
This next example show that applying
eq.subst to a proof of a = b reduces
the goal of showing Blue b to that of
showing Blue a. In a sense, applying 
eq.subst to an equality proof effects
a *rewriting* of the current goal. 
-/
example 
  (Ball : Type)
  (Blue : Ball → Prop)
  (a b : Ball)
  (eq_balls : a = b)
  (a_is_Blue : Blue a) :
  Blue b := 
begin
  -- Study the sequents before and after this step
  apply eq.subst eq_balls,
  assumption,  -- now we can use *this* proof!
end

/-
Lean provides a useful tactic called
rewrite that automates application of
eq.subst to effect such rewritings. The
following two example illustate use of
two different forms of the tactic. In
short, given h : a = b, "rw h" changes
a's in the goal to b's and rw<-h changes
b's in the goal to a's.
-/

example 
  (Ball : Type)
  (Blue : Ball → Prop)
  (a b : Ball)
  (eq_balls : a = b)
  (a_is_Blue : Blue a) :
  Blue b := 
begin
rw<-eq_balls, -- rewrite b to a (right to left)
assumption,
end


-- Exercise: complete the proof
example (α : Type) (a b : α) (P : α → Prop) : a = b → P b → P a :=
begin
intros ab Pb,
end



/- Properties of Relations -- Reflexivity of Equality -/

/-
EXAMPLE: REFLEXIVITY 

In English you can say a relation, r, is reflexive 
if it relates *every* value, x in its "domain" to x 
itself: that is ∀ x, r x x. Remember the relation r 
is specified by a two-place predicate. So ∀ x, r x x 
says that *every* value, x, is related to itself by r.    
-/

#check @reflexive
/-
reflexive : Π {β : Sort v}, (β → β → Prop) → Prop

Π (capital Pi) means universal quantification. So, 
what reflexive says is that "for any type, β (even 
a propositional type), reflexive defines a property 
of any binary relation on β. 

Put another way, if you apply reflexive to any binary 
relation on any type, β (inferred), you will get a 
proposition: the one that precisely expresses what 
it means for such a relation to be reflexive: that 
every element of the domain is related to itself *in 
that relation*.  

For example, the reflexive predicate applied to the 
equality relation yields the proposition that every
value of a given type is related to itself by equality
in this relation.
-/

/- -/

#reduce reflexive (@eq nat)

/- 
Of course, the introduction rule, refl, for equality
*makes* the equality relation reflexive. It's reflexive
by definition and so should be easy to prove.
-/

example : ∀ (X : Type), reflexive (@eq X) :=
begin
assume X,
unfold reflexive,
/- First axiom of equality: 
   X : Type ⊢ ∀ (x : X), x = x
-/
assume x,
-- all the following are equivalent
-- exact @eq.refl X x,  -- no arguments inferred
-- exact eq.refl x,     -- one argument inferred
exact rfl,              -- both arguments inferred
end

/-
Congratulations, you have earned another sticker: this one to
recognize that you are now working with properties of relations
that in turn express properties of sets of ordered pairs of
values. That's sorta cool!
-/

/-
Filling in the implicit arguments and
unfolding the notation gives us the full
picture. See the next definition.
-/
def reflexive' 
  {β : Type} 
  {r : β → β → Prop} := 
  ∀ x, r x x  
/-
These definitions are parameterized by a
type, β, and a (binary) relation, r, on β.
In effect, (r ⊆ β × β), and reflexive' gives
us the  *propositions*, that every value, x, 
of a type β is related to itself by r.
-/


/-
Example:  The statement of and a proof of
the proposition that the equality relation
on natural numbers is reflexive.
-/

example : reflexive (@eq ℕ) := eq.refl


/-
At the same time, the preceding presentation
also seems a little mystifying. Let's see how
we can understand the theorem step by step.
-/

theorem eq_is_refl : reflexive (@eq nat) :=  
-- proof below
/-
Let's unpack the notation, @eq α (where 
in our example, the value of α is ℕ)). 
When we write, 0 = 0, that's infix notation
for the term, eq 0 0 (the application of the
two-place predicate, eq, to 0 and 0. It
is the meaning of the notation 0 = 0.). 

But what (eq 0 0) means is (@eq nat 0 0). 
The first argument of eq is implicit, so 
is usually omitted from code and inferred
from the following values. But here we 
don't give such values. The @tells Lean
to let us write the implicit argument(s)
explicitly. 
-/
begin
  unfold reflexive,
  assume x,
  trivial,    
end

/-
Here's an English version.

Theorem: Equality is reflexive.
Proof. Unfolding the definition of reflexive,
what we are to show is ∀ x, x = x. To prove it,
assume x is an arbitrary value and show x = x.
That's true by (application of) the introduction
rule for equality (to x). QED.

You'd usually leave out the parenthesized
parts, as people with mathematical training,
like you now have, will understand what is
meant implicitly. Indeed, most people would
just say, "and that's trivially true. QED"

Of course an even simpler proof is "by the
reflexivity introduction rule for equality!"

We're just re-proving something we already
knew, be here we're forming the proposition
that equality is reflexivity using a *general*
definition of what that means in the form of
a *predicate on binary relations on any type.*
-/

/-
Note well: reflexive as we're defined it here
is a *one-place* predicate on binary relations, 
which we represent as two-place predicates. So
we expect the type of the reflexive predicate /
property to be (β → β → Prop) → Prop. Lean is
of course plenty smart to already know that!
-/

#check @reflexive

/-
IMPORTANT ASIDE ON FIRST ORDER PREDICATE LOGIC

As an aside that we will return to later, you
cannot express properties of relations, with=
this degree of clarity, in what we call first-
order predicate logic (FOPL). You are expected
to understand FOPL when leaving this course. 
The good news is that it is simply a restricted
form of higher-order predicate logic in which
you are not enabled to quantify over relations.

The syntax of FOPL is simply not capable of 
expressing the kind of idea that we developed
righ there: that we can specify properties of
relations by using our logic.  

From now on, therefore, if you are asked to 
write or prove propositions in first-order 
predicate logic, you can use everything you
have learned, here except that you must not
quantify over functions or relations. In the
case at hand, you would not be allowed to say
"for any binary relation, r, on β" or "there
exists such a relation," because either of
those statements involves quantification over
the set of all binary relations on a type, β.

The broad experience of the computer science
community over the last few decades has shown
that there are many practical benefits to the
use of higher-order logic. In particular, it 
is the logical foundation for automated proof
assistants such as Lean, which are now rapidly
coming into their own, especially for safety-
/ mission- critical sofware, provable system
security, and in the design, analysis, and
implementation of programming languages, as 
well as in attempts to formalize mathematics,
per se.

As you're instructor, I believe, based on a 
decade of work in this area, that the beauty
with which one can express *properties of 
relations* (and the vital importance of this
idea), the availability of automated checking 
of logical syntax and proof correctness (when
doing formal proofs), and that fact that 
first-order logic is simply a restricted form
of higher-order logic, make it *far* preferable 
to FOPL as a logic to learn in a first course
on logic and proof for computer scientists. 

And now we return to our regularly scheduled
programming!
-/

/-
SYMMETRY AS A PROPERTY OF RELATIONS
-/

#check @symmetric
#reduce @symmetric 

/-
Exercise: prove that = is symmetric. And
answer the question, is ≤ symmetric, and
give a brief defense of your answer. If 
your answer is no, provide a counter-example
to show that you are correct.
-/

universe u
theorem eq_is_symm (α : Sort u): symmetric (@eq α) :=
begin
  _     -- You do it
end

/-
TRANSITIVITY AS A PROPERTY OF BINARY RELATIONS
-/

/-
Exercise prove that = is transitive as per
the following formal and general definition
of exactly what that means. Give both formal
and especially informal (mathematical English)
proofs.
-/
def transitive := ∀ ⦃x y z⦄, _

theorem eq_is_trans (α : Sort u): transitive (@eq α) :=
begin
  
end


/-
EQUIVALENCE RELATIONS
-/

end hidden
