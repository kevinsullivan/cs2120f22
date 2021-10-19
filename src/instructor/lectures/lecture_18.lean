import data.set

/-
Up to now we have mostly used our 
intuition to understand operations
on, and special values (empty and
complete) of sets. Now, to prepare
to state and prove theorems about
sets, we will see how to formalize
these ideas in predicate logic. We
isolate our own definitions in a
namespace so as not to conflict 
with the corresponding definitions
from the Lean libraries. 
-/

namespace hidden

/-
We define the concept of a set
of values of type α as nothing
other than a predicate on values
of this type. (Previously we've
used T as a type parameter but
lower case Greek letters are also
often used for this purpose.)
-/
def set (α : Type) := α → Prop

/-
And given any one-place predicate
on α, we can view it as defining
a set.
-/

def set_of {α : Type} (p : α → Prop) : set α := p

/-
For the rest of this section, the
following declaration allow us to
use α and β as arguments without 
having to introduce them explicitly
in each definition. The way it works
is that if α appears in a definition,
Lean will silently add "∀ {α : Type}"
as an argument to the definition.
-/ 

variables {α β : Type} 

/-
Membership of a value a in a set s
is defined by the proposition, s a,
obtained by applying the membership
predicate, s, to the value a. If the
resulting proposition is true then a
is in s. If (s a) is false, a's not
in s.
-/

def mem (a : α) (s : set α) :=
s a

/-
Note: The use of α in the previous
definition causes Lean to insert a
declaration, (α : Type), in the 
definition. So the definition is
actually equivant to the following:

def mem (α : Type) (a : α) (s : set α) :=
s a
-/

/-
a ∈ s is simply notation for the
proposition (mem s a), which in 
turn is just (s a). See preceding
definition. 
-/

notation a ∈ s := mem a s
notation a ∉ s := ¬ (mem a s)

/-
We can now formally define what we
mean when we say that a set, s₁, is
a subset of a set, s₂: that if any
value, a, is in s₁ then it is also
in s₂. For example, s₁ = {1, 2} is a 
subset of s₂ = {1, 2, 3, 4} because
any value being in s₁ implies that
it is also in s₂. 1 is in s₁ and it
is also in s₂, and the same goes for
2. Those are all the values in s₁, 
so for any value, if it's in s₁ it's
also in s₂, so s₁ is a subset of s₂.
-/
def subset (s₁ s₂ : set α) :=
∀ ⦃a : α⦄, a ∈ s₁ → a ∈ s₂

/-
You can read the curly braces in
⦃a : α⦄ as if they were ordinary 
{a : α} braces. They tell Lean to
infer these arguments. There's a 
subtle technical differences that
is not important here.
-/

notation s₁ ⊆ s₂ := subset s₁ s₂

/-
It is common in predicate logic to 
talk about all the subset of elements
in a set, s, that satisfy a predicate,
p. Here's a function that when given
a predicate and a set (with the right
types) returns the set (as a predicate,
of coures) of elements in s that also
satisfy p.
-/
def sep (p : α → Prop) (s : set α) : set α :=
{a | a ∈ s ∧ p a}

/-
Exercise: Given the assumptions that 
evens and primes are sets of natural
numbers, write an expression for the 
subset of evens that are also prime.
-/
axioms (evens primes : ℕ → Prop)
def even_primes : set ℕ := _

/- 
Exercises: 

1) Express sep evens primes in English

-- answer

2) Assume that evens really is the set
of even natural numbers and primes is 
the set of prime numbers. What set of
values is in even_primes? 
-/

/-
The empty set of values of any given
type is defined by the predicate that
is false for each value of that type.

Here we express this predicate as the
function that, when given any value, 
a, of type α, returns false. The type
of this function is α → false, and so
it is, we now see clearly, a predicate. 
No value satisfies it, so it represents
the set with no values, the empty set
for the type, α. 
-/

def empty_set {α : Type} (a : α) := false

#check @empty_set

def empty_nat : set ℕ := empty_set

/-
To understand the preceding definition
of empty_set takes a little help. It 
takes two arguments, the first, α, is 
a type, which is *implicit* (inferred
from context), and the second is a value
of 
-/

/-
 Here's another notation, new for you in
 this class. Read the λ as meaning ∀: in
 other words, given a value, a, of type,
 α, this function returns the proposition,
 false. λ is the symbol used to declare
 the arguments of a function. The overall
 expression, λ (a : α), false, is called
 a lambda expression, It denotes exactly
 the funciton that takes any a and returns
 the proposition, false (which, again, of
 course, is of type α → Prop), making it a
 predicate, and one that defined the empty
 set. 

 FIX
-/

def empty_set' : set α := 
  λ (a : α), false

-- The notation φ is used for empty set
def φ := empty_set α

#check empty_set α

/-
The complete, or *universal* set of values
of a type α is defined similarly, but now
we use a proposition that is true for every
value, making every value of a given type a
member of the set.
-/

def univ : set α :=
λ a, true

/-
We can even start to define functions that
look a little like "imperative" operations,
mutator functions, on sets. Here we define
an insert operation that takes a set and a
value, both of the same type, and returns
a new set with the members of the given set
and the new value as its members.
-/

def insert (a : α) (s : set α) : set α :=
{b | b = a ∨ b ∈ s}

-- example
def primes_and_15 := insert 15 primes

/-
A set with exactly one member value is 
called a *singleton* set. Here we define
the singleton set containing a value a as
a set of values all of which are equal to
a.
-/

def singleton (a : α) : (set α) := 
  {b | b = a}

/-
Now we come to the standard operators on
sets: union, intersection, etc. First the
union of two sets, s₁ and s₂ is the set of
values that satisfy the disjunction (or) 
of the individual sets. Thus a value is
in the resulting set if and only if it's
in one of the contributing sets. 
-/

def union (s₁ s₂ : set α) : set α :=
{a | a ∈ s₁ ∨ a ∈ s₂}

notation s ∪ t := union s t 

/-
Intersection is defined similarly but now
an element is in the resulting set if and
only if it's in both of the contributing
sets.
-/

def inter (s₁ s₂ : set α) : set α :=
{a | a ∈ s₁ ∧ a ∈ s₂}

notation s ∩ t := inter s t

/-
The complement of a set of values of type 
α is the set of elements of this type that
are not in the given set.
-/

def compl (s : set α) : set α :=
{a | a ∉ s}

/-
Given sets, s and t, the difference,
s \ t, is the set of elements in s that
are not in t. You can think of this as
"s take away t." It's analogous to the
idea of subtraction, where, for example,
5 - 2 means 5 take away 2.
-/

def diff (s t : set α) : set α :=
{ v | v ∈ s ∧ v ∉ t}

/-
Powerset
-/

def powerset (s : set α) : set (set α) :=
{t | t ⊆ s}

-- Question: What's the type of t, here?

-- notation 𝒫 s := powerset s

/-
Finally, here's a new concept for you, 
and one that foreshadows our upcoming
discussion of functions. The image of 
a set, s, under a function f, is the 
set of values obtained by applying f
to every value in s. 
-/

def image (f : α → β) (s : set α) : set β :=
{b | ∃ a, a ∈ s ∧ f a = b}

/-
The formal definition sort of goes to a 
next level of sophistication in the use
of predicate logic. It says that the image
of the set, s, "under" the function, f, 
is the set of values, b, such that there
is (exists) some value, a ∈ s, f a = b.
-/


end hidden
 
