import .lecture_23 

/-
UNIVERSAL QUANTIFICATION OVER AN EMPTY SET IS TRUE

Let's review the most puzzling of the examples from
last time: a relation r = {(0,1), (2,3)} we said is
transitive because it satisfies the constraint that
defines transitivity: for every x, y, and x, if (x,y)
is in r, and (y,z) is in r, then (x,z) is in r. This
relation is transitive because in *every* case where
we have (x, y) and (y, z) in r, (x, z) is in r. In
this example, there are *no* such cases, and so the
predicate is satisfied!

Let's think about this principle using a different
example. Question: is every ball in an empty bucket
of balls red?
-/

axioms (Ball : Type) (red : Ball → Prop)
def empty_bucket := ({} : set Ball)
lemma  allBallsInEmptyBucketAreRed : 
  ∀ (b : Ball), b ∈ empty_bucket → red b := 
begin
  assume b h,
  _             -- finish off this proof
end

/- 
Whoa, ok. That's a little bit counterintuitive, but
it's correct. A universal quantification over an empty
set is always trivially true. Here's another way to 
think about it. Suppose we had a set with two balls
in it: { b1, b2 }. To show that every ball is red,
we'd show that b1 is red, AND (∧) that all balls in 
the remaining set, { b2 }, are red. To prove the 
latter, we'd show that b2 is red, and that all balls
in the remaining set, {}, are red. So we have that
all balls are red if (red b1) ∧ (red b2) ∧ "all balls
in {} are red". If b1 and b2 really are red, then
that last predicate better be true if the whole chain
of ∧ operations are to be true. When you think about
∀ as a version of ∧ that can take any number of
arguments, not just 2, it becomes clear that when
applied to zero arguments, the answer better be true,
otherwise this operation would *always* return false.  
-/

/-
So now let's revisit once again our funny example of
transitivity: { (0,1), (2,3) }. There are no cases 
here where we have both (x,y) and (y,z) as pairs in
this relation, so there are no cases to consider, so
the transitivity property holds by the definition of
∀ (and for ∧, if you want to think of ∀ as a multi-
argument version of ∧, taking anywhere from zero to
an infinite number of arguments).

Question: Is this symmetric? {(0,1), (1,0), (2,2)}
How about this: {(0,1), (1,0), (2,2)}?

Now suppose that we have a relation, r, over a set
of values, {0, 1, 2, 3, 4, 5}. Is this relation
reflexive? {}

Question: If a relation is transitive and symmetric
is it necessarily reflexive? If so, give an informal
argument/proof. If not, give a counter-example. 
-/

/-
CLOSURE OPERATIONS ON RELATIONS

Given a relation, r, the reflexive, symmetric, or
transitive closure of r is the smallest relation that
(1) contains r, and (2) contains any additional pairs
needed to make the resulting relation reflexive, or
symmetric, or transitive, respectively. The reflexive,
symmetric, transitive closure of r is the smallest
relation (which means *no* unnecessary added pairs)
that contains r and has all three properties. Note
that the resulting relation will be an equivalence
relation. The meaning of this is basically that if
anything is connecting to somethiing else, they will
end up in the same "equivalence class." We'll see a
picture.
-/

def reflexive_closure := λ (a b : β), (r a b) ∨ (a = b)
def symmetric_closure := λ (a b : β), (r a b) ∨ (r b a)

/-
Let's look examples. What's in the reflexive closure
of { (0,1), (1,2), (2, 3), (3, 4), (4, 5) }? It is 
often easier to think about these things with the aid
of a picture, so let's draw this relation and see in
graphical terms what it means to compute its reflexive
closure.
-/

/- 
The definitions of the reflexive and symmetric closures
of a relation are pretty easy to state. It's a little 
harder to say what set of pairs is in the transitive
closure of a given relation, r. Clearly it's a relation, 
r', where r' is the smallest relation that contains r 
and that is transitive. In other words, (tc r) is r
with any additional pairs needed to make the result
transitive.

What set of pairs is this? Well, (1) it contains every
pair in r, and (2) if (a,b) is in (tc r) and if (b, c)
is in (tc r), then (a, c) must also be in r. The way we
will say this formally uses what we call an inductive
definition. Inductive definitions allow for "bigger"
things to be built whenever there are smaller things
of the right kind.

Consider this relation, r = { (0,1), (1,2), (2, 3) }.
It's transitive closure clearly contains all three of
these pairs. What else must it include at a minimum to
be transitive?

Consider r = { (0,1), (1,2), (2, 3), (3, 4), (4, 5) }.
What is its transitive closure?

In plain English, if there's a "path" of pairs between 
two values, a and c, e.g., by way of b where (a,b) and 
(b,c) are in the relation, then (a,c) will also be in
the relation, i.e., the direct connection, (a,c), will
also be in the relation. 

The following formal definition is not one that I 
expect you to understand immediately, as we have not
yet introduced iductive definitions, of which this is
an example. But you can just read it as definining
the introduction rules, base and trans, for proving
one relation is the transitive closure of another, r.

The first rule says that if any two objects, a and b,
are related in r, then they are also related in tc r
(the transitive closure of r). The second rule says 
that if objects a and b are related in (tc r) and b
and c are related in (tc r) then a and c must also 
be related in r. For any length-2 "path" from a to c
(via b), then there's a direct connection: (a,c) ∈ r. 
-/
inductive tc {α : Type} (r : α → α → Prop) : α → α → Prop
| base  : ∀ a b, r a b → tc a b
| trans : ∀ a b c, tc a b → tc b c → tc a c

/-
Here's a possibly surprising fact: the transitive 
closure concept *cannot be expressed, defined, nor the
concept used, in first-order predicate logic*. The
reason is that you can't quantify over relations, and
so cannot write "for any relation, r, it's transitive 
closure is ..." Quantifying over relations just isn't
allowed: it's not even part of the syntax of first-
order predicate logic.

Yet what we've written, formally and understandably, is
a concept essential in all kinds of logical reasoning in 
computer science. That suggests something about teaching
first-order logic as a first logic for computer science:
there's real reason to doubt that it's the best choice.
The higher-order predicate logic of Lean and similar
modern proof assistants is strictly more expressive.
-/


/-
ORDERING RELATIONS
-/

namespace relations

section relation

/-
Define relation, r, as two-place predicate on 
a type, β, with notation, x ≺ y, for (r x y). 
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  

/-
-/
def strict_ordering :=  asymmetric r ∧ transitive r
def ordering :=         reflexive r ∧ anti_symmetric r ∧ transitive r
def partial_order :=    reflexive r ∧ anti_symmetric r ∧ transitive r ∧ ¬ total r
def total_order :=      reflexive r ∧ anti_symmetric r ∧ transitive r ∧ total r

/-
Exercise: We started our discussion of properties of binary relations on 
values of a type, β, with the case of what it means for such a relation to
be total: that every pair of objects is related at least in one direction
or the other. Think of this as saying that any two objects are comparable.
In the less-or-equal relation on natural numbers, you can compare any pair
of natural numbers. The subset inclusion relation, on the other hand, is
not total. It is said to be partial. 

Consider the subset relation on the powerset of {0, 1}, that is, on the
sets {0, 1}, {0}, {1}, {}. The subset relation is not total. Its elements
are ({},{}), ({}, {0}), ({}, {1}), ({}, {0,1}), ({0}, {0}), ({0}, {0,1}),
({1}, {0,1}) ({0,1}, {0,1})}
-/

/-
Definitions vary subtly. Be sure you know what is meant by these terms in any
given setting or application.
-/

end relation
end relations
