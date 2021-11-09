/-
OPERATIONS ON BINARY RELATIONS

We now introduce three basic operations on binary
relations. In this short section, we generalize to
binary relations *from* one type *to* another. In
this setting we consider three operations:
-/

namespace relations
section relation

variables (α β γ : Type)

def inverse 
  (r : α → β → Prop) : 
      (β → α → Prop) :=
λ x y, r y x


def image 
  (r : α → β → Prop) 
  (s : set α) : 
  set β :=
  { b : β | ∃ (a : α), a ∈ s ∧ r a b }  

/-
Exercise: Formally define the preimage of a
set, s : set β, under a relation, r : α → β.
The preimage of s is the set the of α values 
with corresponding β values under r.  
-/ 

def composition 
  (r : α → β → Prop) 
  (s : β → γ → Prop) : 
      (α → γ → Prop) :=
λ a c, ∃ b, (r a b) ∧ (s b c) 

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

end relation
end relations
