/-
To make sense of this you need to know about *relations*, for which you need these concepts:
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
-/

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
A binary relation is specified by a
two-place predicate. In other words,
you can think of it as a function that
takes two values and yields a proposition
about them. Equality is such a relation.
You can write x = y, but you can also
write eq x y to mean the same thing.
Writing it this way makes it clear
that equality takes two arguments
and returns a proposition.

Examples:
  eq 3 4 -- the proposition that 3 = 4
  eq 3 3 -- the proposition that 3 = 3

You can understand the following 
general explanation by taking eq as
a possible relation in place of "R"
in the following.
-/

-- We've already assumed T can be any type

-- Next assume we have an arbitrary binary relation, R, on T
axiom R : T → T → Prop

-- here's a formal definition of what it means for R to be reflexive
def rel_reflexive := ∀ (x : T), (R x x)

def rel_symmetric := ∀ (x y : T), (R x y) → (R y x)

def rel_transitive :=
  ∀ (x y z : T), (R x y) → (R y z) → (R x z)

/-
So now, from only our two axioms, let's prove that
equality is not only reflexive, but also symmetric
and transitive!
-/

