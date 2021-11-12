/-
BACK TO PROPERTIES OF RELATIONS
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
({1}, {0,1}) ({0,1}, {0,1})}. Draw these sets as "nodes" in a graph and
the pairs as directed edges between the nodes. Is the relation depicted
in this way a total order? A partial order? What properties does it have?
-/

/-
Definitions vary subtly. Be sure you know what is meant by these terms in any
given setting or application.
-/


/-
Exercises: show that image and preimage
preserve some important properties and 
not others.
-/

/-
Formally define what it means for a relation
to be a well-order.
-/

example : 
  function r → 
  surjective r → 
  image_set r (dom r) = { b : β | true} :=

begin
  unfold function surjective image_set dom,
  assume f s,
  apply set.ext,
  assume x, 
  split,
  
  -- forward
    assume h,
    exact true.intro,

  -- backward
    assume h,
    cases s with svr sur,
    have exa := sur x,
    cases exa with a pfa,
    -- rewrite goal to a simple, definitionally equal version
    show ∃ (a : α), a ∈ {a : α | ∃ (x : β), r a x} ∧ r a x,
    apply exists.intro a,
    split,
    show ∃ (x : β), r a x,
    apply exists.intro x,
    assumption,
    assumption,
end

example : bijective r → function (inverse r) :=
begin
  unfold bijective function inverse,
  unfold surjective injective single_valued function,
  assume bij,

  cases bij with surf injf,
  cases surf with sv sur,
  cases injf with sv inj,

  -- show that result is single_valued
  assume x y z,
  assume ryx rzx,
  exact inj ryx rzx,
end