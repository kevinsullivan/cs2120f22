import .lecture_24

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
def ordering :=         reflexive r ∧ transitive r ∧ anti_symmetric r
def partial_order :=    reflexive r ∧ transitive r ∧ anti_symmetric r ∧ ¬ strongly_connected r
def total_order :=      reflexive r ∧ transitive r ∧ anti_symmetric r ∧ strongly_connected r

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


/-
OPERATIONS ON RELATIONS - WIP
-/

-- inverse
-- image
-- composition

end relation
end relations
