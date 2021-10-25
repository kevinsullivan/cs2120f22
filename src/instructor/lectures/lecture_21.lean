
import data.set

namespace hidden 


/-
PROPERTIES OF RELATIONS
-/


section relation

/-
For any types, α and β we will refine a
relation, r, to be a predicate on values
of these types. It will implicitly define
the set of all such pairs, also called a
relation, that satisfy the predicate (by
yielding a proposition for which there is
a proof).
-/

variables {α β : Type}  (r : β → β → Prop)
/-
This variables declaration implicitly adds
the following parameters to the front of 
each definition below, as needed based on
the variables used in the rest of a given
definition. We'll see an example shortly.
-/

#check r   -- two place predicate: relation

/-
We will introduce an infix notation, ≺, 
for the relation/predicate, r, so that
instead of writing (r a b) to denote 
the proposition that a is related to b
by r, we can write (a ≺ b) read as "a
is related to b." 
-/
local infix `≺`:50 := r   -- infix notation

/-
With these concepts and notations, we
can now define many essential properties 
of relations in an entirely general way.
-/


/-
REFLEXIVITY AS A PROPERTY OF RELATIONS
-/

/-
Let's see an example in detail. Using the
preceding definitions, implict arguments,
and notations, the definition of reflexive
is exceedingly clear. This is it. In English
you can say "a relation, ≺, is reflexive if 
it relates every value, x, to itself.""
-/
def reflexive := ∀ x, x ≺ x

/-
Filling in the implicit arguments and
unfolding the notation gives us the full
picture. See the next definition.
-/
def reflexive' 
  {β : Type} 
  {r : β → β → Prop} := 
  ∀ x, r x  x
/-

These definitions are parameterized by a
type, β, and a (binary) relation, r, on β
(r ⊆ β × β), and the yield *propositions*,
that every value of a type β is related to
itself by r.

One will often then want a proof, but now
that is just a matter of ordinarly logical
reasoning. We have thus now "reduced" one
crucial property of mathematial relations
to our underlying predicate logic.   

As an example, let's state and prove the
proposition that the equality relation for
natural numbers is is reflexive.
-/

theorem eq_is_refl : reflexive (@eq nat) :=  
-- proof below
/-
Let's unpack the notation, @eq α. When we 
write, 0 = 0, that's infix notation for
the term, eq 0 0 (the application of the
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
that equality is reflexivity using a general
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

Again, think of Π as ∀. What defined reflexive
to be, given any type β, is a predicate on binary
relations on β. Some binary relations are reflexive, 
some aren't: i.e., some have the property of being
reflexive (of reflexivity), some don't. 

This predicate picks out (logically) those that do. 
Building on our discussion of sets, it appears to
be the case, and it is, that it defines the set of
binary relations on β that are reflexive. We can
define this set explicitly by using reflexive as a
predicate on binary relations in a set builder
expression.
-/

def reflexive_relations := 
  { r : β → β → Prop | reflexive r }

-- That's pretty cool. Says a lot, very precisely.

/-
Now we can even state and prove theorems about
relations being reflexive, using the language
of *set theory*. Here we say that "the equality
relation on natural numbers is an element in
the set of all reflexive binary relations on
the natural numbers." Here it is formally. The
use of @ here again turns off implicit argument
inference. I do expect you to understand what it
means when you see it. I will not give you any
problems, except perhaps extra credit, where I
expect you to know when exactly to use it. 
-/
example : @eq nat ∈ @reflexive_relations nat := 
begin
  show reflexive_relations (@eq nat),
  unfold reflexive_relations,
  exact eq_is_refl,      -- Already proved, use theorem!
end
-- You can just feel your brains getting bigger here!

#check (λ x, x + 1)


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
give a brief defense of your answer.
-/

theorem eq_is_symm : symmetric (@eq α) :=
begin
end

/-
Exercise prove that = is transitive as per
the following formal and general definition
of exactly what that means. Give both formal
and especially informal (mathematical English)
proofs.
-/
def transitive := ∀ ⦃x y z⦄, x ≺ y → y ≺ z → x ≺ z

example : transitive (@eq α) :=
begin
end

/-
Here's a new concept: a relation is said to be an
equivalence relation if it is reflexive, symmetric,
and transitive. 
-/
def equivalence := reflexive r ∧ symmetric r ∧ transitive r

lemma mk_equivalence (rfl : reflexive r) (symm : symmetric r) (trans : transitive r) :
  equivalence r :=
⟨rfl, symm, trans⟩

-- Exercise
theorem eq_is_equivalence : equivalence (@eq β) :=
begin
end

/-
ADDITIONAL PROPERTIES OF RELATIONS. NEXT LECTURE.
-/

def total := ∀ x y, x ≺ y ∨ y ≺ x

def irreflexive := ∀ x, ¬ x ≺ x

def anti_symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y

def empty_relation := λ a₁ a₂ : α, false

def subrelation (q r : β → β → Prop) := ∀ ⦃x y⦄, q x y → r x y

def inv_image (f : α → β) : α → α → Prop :=
λ a₁ a₂, f a₁ ≺ f a₂

lemma inv_image.trans (f : α → β) (h : transitive r) : transitive (inv_image r f) :=
λ (a₁ a₂ a₃ : α) (h₁ : inv_image r f a₁ a₂) (h₂ : inv_image r f a₂ a₃), h h₁ h₂

lemma inv_image.irreflexive (f : α → β) (h : irreflexive r) : irreflexive (inv_image r f) :=
λ (a : α) (h₁ : inv_image r f a a), h (f a) h₁

inductive tc {α : Type} (r : α → α → Prop) : α → α → Prop
| base  : ∀ a b, r a b → tc a b
| trans : ∀ a b c, tc a b → tc b c → tc a c

end relation

end hidden
