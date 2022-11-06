
import logic.relation

namespace hidden 


/-
PROPERTIES OF RELATIONS
-/


section relation


-- variables 
-- {α β : Type}  
 -- (r : β → β → Prop)

/-
Let α and β be data types and suppose r 
is a binary relation on values of type, β. 
-/


/-
Wewill introduce an infix notation, ≺, for
r. So instead of writing r x y we can write
x ≺ y ("x 'precedes' y in the relation"), or
"x is related to y by r."
-/
-- local infix `≺`:50 := r   -- infix notation

/-
-/

/-
REFLEXIVITY: A PROPERTY OF BINARY RELATIONS
-/

/-
Let's see an example in detail. Using the
preceding definitions, implict arguments,
and notations, the definition of reflexive
is exceedingly clear. This is it. In English
you can say "a relation, ≺, is reflexive if 
it relates every value, x, to itself.""
-/

def reflexive {β : Type} (r : β → β → Prop) : Prop := ∀ x, r x x
#check @reflexive

/-
For any type, β (implicit), reflexivity is a property of any
binary relation, r, on β, defined by the predicate requiring
every object of this type to be related to itself in/by r. 

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
  ∀ x, r x x  -- equivalently ∀ x, x ≺ x
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
That's actually very interesting: it says
that eq.refl is a proof that equality on 
the natural numbers is reflexive, where
reflexive as defined here can be applied
to any binary relation on any type, β, to
express the proposition that that relation
is reflexive.   
-/


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
Π {β : Type}, (β → β → Prop) → Prop

Again, think of Π as ∀. We define reflexive, given 
a type β, to be a predicate on binary relations on 
β. Some relations are reflexive,some aren't: some
have the property of being reflexive (reflexivity),
some don't. The reflexive predicate "picks out" the
relations that have this property: it's the ones
for which there is a proof. And once we've defined
reflexive as a predicate on relations, we can even
talk about the *set of all reflexive relations on 
values of a given type, β.* Here is how we write 
this set using reflexive as a predicate in a set
builder expression.
-/

def reflexive_relations := 
  { r : β → β → Prop | reflexive r }

-- That's cool. It says a lot very concisely.

/-
Now we can even state and prove theorems about
relations being reflexive using the language
of *set theory* by asserting that a relation 
is *in this set* 
-/
example : @eq nat ∈ @reflexive_relations nat := 
begin
  -- next three lines optional, for pedagogical clarity
  show reflexive_relations eq,
  unfold reflexive_relations,
  show reflexive (@eq nat),
  exact eq_is_refl,      -- Already proved, use theorem!
end


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


def symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x

/-
Exercise: prove that = is symmetric. And
answer the question, is ≤ symmetric, and
give a brief defense of your answer. If 
your answer is no, provide a counter-example
to show that you are correct.
-/

theorem eq_is_symm : symmetric (@eq α) :=
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
def transitive := ∀ ⦃x y z⦄, x ≺ y → y ≺ z → x ≺ z

theorem eq_is_trans : transitive (@eq α) :=
begin
  unfold transitive,
  assume x y z h1 h2,
  exact eq.trans h1 h2,
end


/-
EQUIVALENCE RELATIONS
-/

/-
Here's a new concept: a relation is said to be an
equivalence relation if it is reflexive, symmetric,
and transitive. 
-/
def equivalence := reflexive r ∧ symmetric r ∧ transitive r

-- A convenience function for proving equivalence
def mk_equivalence (rfl : reflexive r) (symm : symmetric r) (trans : transitive r) :
  equivalence r :=
⟨rfl, symm, trans⟩

#check @mk_equivalence
#check @eq_is_refl

example : equivalence (@eq nat) := 
  @mk_equivalence ℕ eq     -- type inference fails so need explicit args here
    eq_is_refl
    eq_is_symm
    eq_is_trans

end relation

end hidden
