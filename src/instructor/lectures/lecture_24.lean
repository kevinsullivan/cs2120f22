import .lecture_23 

variables {α β : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  

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
  cases h,             -- finish off this proof
end

/- 
Whoa, ok. That's a little bit counterintuitive, but
it's correct. A universal quantification over an empty
set is always trivially true. 


Here's another way to think about it. Suppose we had 
a set with two balls in it: { b1, b2 }. To show that 
every ball is red, we could use case analysis: break
the task into two cases: show that b1 is red, AND 
show that all balls in the remaining set, { b2 }, are
red. 

To prove the latter, we'd show that b2 is red, and 
that all balls in the remaining set, {}, are red. 
So we have that all balls are red if (red b1) ∧ 
(red b2) ∧ "all balls in {} are red". 

If b1 and b2 really are red, then the last proposition
better be true if the whole chain of ∧ operations is to 
be true. When you think about ∀ as a version of ∧ that
can take any number of arguments, not just 2, it becomes
clear that when applied to zero arguments, the answer 
really has to be true, otherwise this operation would
*always* produce propositions that are ultimately false.  
-/

/-
So now let's revisit once again our funny example of
transitivity: { (0,1), (2,3) }. There are no cases 
here where we have both (x,y) and (y,z) as pairs in
this relation, so there are no cases to consider. 
When there are no cases to consider, the conclusion
holds in all cases, of which there are 0, so it holds.

Question: Is this symmetric? {(0,1), (1,0), (2,2)}
How about this: {(0,1), (1,0), (2,3)}?

Now suppose that we have a relation, r, over a set
of values, {0, 1, 2, 3, 4, 5}. Is this relation
reflexive? {} What about this: {(0, 1), (2, 3)}

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
symmetric, or transitive, respectively. 

The reflexive, symmetric, transitive closure of 
r is the smallest relation that contains r and 
has all three properties. Note that the resulting
relation will be an equivalence relation. 
-/

-- REFLEXIVE CLOSURE

/-
A pair (a, b) is in the reflexive closure of r if
(a, b) is in r or if (a = b).
-/
def reflexive_closure := λ (a b : β), (r a b) ∨ (a = b)

/-
Exercise: what pairs are in the reflexivee closure of
the following relation, r, over the set {0, 1, 2}?

r = {}
-/

-- SYMMETRIC CLOSURE

/-
A pair (a, b) is in the symmetric closure of r if 
(a, b) is in r or if (b, a) is i r.
-/
def symmetric_closure := λ (a b : β), (r a b) ∨ (r b a)

/-
Consider a set, s = {0, 1, 2, 3} and a binary relation
on s, r = {(0,1),(3,2)}. What pairs are in the symmetric
closure, (sc r), of r. Clearly (0,1) and (3,2) are in
(sc r), because they are in r. But are (1,0) and (2,3) in
sc r, as we expect? Let's apply symmetric_closure to a=1
b=0. This pair is defined to be in the *closure* if the
resulting proposition is true. The proposition is (a,b)
is in r or (b, a) is in r. Clearly (a=1,b=0) is not in r,
but (b=0,a=1) is in r, so (a=1,b=0) is (defined to be)
in (sc r). In a nutshell, the symmetric closure includes
an edge/pair if either it is in r, or its reverse is r.
-/

/-
Let's look examples. What's in the reflexive closure
of { (0,1), (1,2), (2, 3), (3, 4), (4, 5) }? It is 
often easier to think about these things with the aid
of a picture, so let's draw this relation and see in
graphical terms what it means to compute its reflexive
closure.
-/

-- TRANSITIVE CLOSURE

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

namespace hidden 

inductive tc {α : Type} (r : α → α → Prop) : α → α → Prop
| base  : ∀ a b, r a b → tc a b
| trans : ∀ a b c, tc a b → tc b c → tc a c

end hidden

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
