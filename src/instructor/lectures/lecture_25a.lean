import .lecture_24

/-
BASIC SETUP
-/
namespace relations
section relation

-- Assume a binary relation, r, written x ≺ y
variables {α β γ : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  

/-
ORDERING RELATIONS ON A TYPE, β 
-/

def strict_ordering :=  asymmetric r ∧ transitive r
def ordering :=         reflexive r ∧ transitive r ∧ anti_symmetric r
def partial_order :=    ordering r ∧ ¬strongly_connected r
def total_order :=      ordering r ∧ strongly_connected r
-- Note: strongly connected means the same thing as total in this context

/-
Exercise: Formalize the concept of a well-order.
From Wikipedia: In mathematics, a well-order (or
well-ordering or well-order relation) on a set S
[of objects of type β] is a total order on S with 
the property that every non-empty subset of S has
a least element in this ordering.
-/

def well_order := total_order r ∧ _

end relation
end relations
