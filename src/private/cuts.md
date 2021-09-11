
The rest of this section will unpack what
that means. It will cover:

- What it means to say that equality is a relation
-
- How the axioms define the very interesting binary relation of equality

- From these axioms we can deduce (prove!) that equality must also be:
  - symmetric (T : Type) ∀ (a b : T), a = b ↔ b = a
  - transitive: ∀ (T : Type), ∀ (a b a : T), a = b → b = c → a = c
  - equivalence: reflexive ∧ symmetric ∧ transitive

- One then talk about "equivalence classes", and that's a beautiful and important concept

To make sense of this you need to know about *relations*. And to understand relations, you first need these concepts:

- set/type (e.g., ℕ, ℝ, ℚ, etc, but also bool, string etc.)
  
- products of sets/types: a set/type of ordered pairs of objects of the given types
  
- the big one: a *binary relation* is any subset of a product two sets/types: R ⊆ S × T

- a binary relation on *a* set/type, T, is a binary relation, R ⊆ T × T

- relations can be defined by stating a membership property on the ordered pairs

- Here are some examples of properties of an ordered pair, (x, y)
  - the property of being equal, that x = y
  - the property that x < y
  - the property that y = x^2
  - the property that x^2 + y^2 = 1
  - the property that y is the hailstone sequence length for x
  - the property that if x is even y is zero and otherwise y is one
  - etc.


/-
To make it concrete, let's see what the equality relation
(on (pairs of) natural numbers) looks like as a subset of
the product set/type of ℕ and ℕ. 

The concept of a product set is simple. It's a multiplication
table. To visualize the product set/type of sets/types S and 
T, list the elements of S on one axis, the elements of T on
the other axis, and at the intersections in the columns with
the rows, just write down the corresponding ordered pairs. 
The set of ordered pairs belong to the product set/type. The
following chart illustrates where both S and T are ℕ. So
this is a visualization of the set/type ℕ × ℕ. 

                      ℕ × ℕ 
  ℕ   0     1     2     3     4     5   ...
  0 (0,0) (0,1) (0,2) (0,3) (0,4) (0,5) ...
  1 (1,0) (1,1) (1,2) (1,3) (1,4) (1,5) ...
  2 (2,0) (2,1) (2,2) (2,3) (2,4) (2,5) ...
  3 (3,0) (3,1) (3,2) (3,3) (3,4) (3,5) ...
  4 (4,0) (4,1) (4,2) (4,3) (4,4) (4,5) ...
  5 (5,0) (5,1) (5,2) (5,3) (5,4) (5,5) ...
...

You might be intersted to know that Lean supports the standard
mathematical notation's we're using here: the product of types
and ordered pairs as values of these types. Here are examples,
using the integers, ℤ, rather than the nats.
-/

def E  : ℤ × ℤ := (1, 0)
def NE : ℤ × ℤ := (1, 1)
def N  : ℤ × ℤ := (0, 1)
def NW : ℤ × ℤ := (-1, 1)
def W  : ℤ × ℤ := (-1, 0)
def SW : ℤ × ℤ := (-1, -1)
def S  : ℤ × ℤ := (0, -1)
def SE : ℤ × ℤ := (1, -1)

/-
In general, the two sets/types in a product don't
have to be the same, but here we're focusing on the
equality relation, which relates elements of a set
to elements of that same set. So fo rnow we're going
to focus on the special case of relations *a* given
set/type.
-/


/-
Knowing what a product set/type looks like is
easy: it's the set of *all* possible ordered
pairs, filled in just like in the table above.

When we define a relation, on the other hand,
we might have to specify (mathematically) some
fairly complex *property* that characterizes
all and only those pairs in the desired subset
of the produt set!

So we are at the point where it makes sense to
introduce a notation for describing relations,
in general. If T is a set/type, then a binary
relation on T is the subset of ordered pairs of
type T × T that have some property: if it has
the property, it's in the set, and if it's in
the set, it has the property.

Here as an example is how we'd specify the
equality relation as the subset of ordered
pairs of natural numbers, such that the two
elements are equal: { (x,y) : ℕ × ℕ | x = y }
-/

def f := { p : (ℕ × ℕ) | p.1 = p.2 }

/-
f is the set of p's, orderer pairs of
natural numbers, such that the first 
element of p is equal to the second.
-/

#check f

/-
And there you go: Lean recognizes f
as a set of pairs of natural numbers.
-/

/-
Practice:
1. Define l to to be the set of pairs of natural
numbers where the first is less than or equal to
the second (in Lean).
-/

/-
2. Define s to be the set of pairs of natural
numbers where the second is the square of the
first.
-/

/-
INFERENCE RULE #1/2: EQUALITY IS REFLEXIVE

Everything is equal to itself. A bit more formally,
if one is given a type, T, and a value, t, of this
type, then you may have a proof of t = t "for free."
-/

axiom eq_refl  : 
  ∀ (T : Type)  -- if T is any type (of thing)
    (t : T),    -- and t is thing of that type, T
  t = t         -- then you get a proof of t = t in return

/-
Ok, you actually have to *apply* the axiom of
reflexive equality. 
-/

example : 1 = 1 := eq_refl ℕ 1  -- Our definition
example : 1 = 1 := eq.refl 1    -- Lean's definition (T is inferred)

/-

ensure that we never use objects of one type
where objects of another type are required. We
want a statically type-checked predicate logic.
That is what type theory does for you logically.
One of the things Lean provides us with is an
embedding of the language of predicate logic
into the more abstract logic of Lean itself.]
