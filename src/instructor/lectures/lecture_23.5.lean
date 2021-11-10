/-
A challenging example that we considered recently
was the question whether a relation {(1,2),(4,5)}
is transitive. It is because it is a model of the
constraint that defines transitivity: a universal
generalization of a conditional. For every three
possible objects, a, b, and c, if the pair (a,b) 
is in the relation, and (b,c) is, too, only then
must the relation also contain the pair (a,c), if
it is to be transitive. But in the case where there
are *no* instances of pairs, (a,b) and (b,c), with
a common, pair-joining element, b, then there are
no cases in which there needs to be a third pair.
In this unit we just strengthen the idea that you
already have that a univeral genealization (a ∀)
over an empty set is always true, and that makes
sense because there are no cases that individually
have to satisfy the given constraints.
-/

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

