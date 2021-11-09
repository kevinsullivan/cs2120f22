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

def strict_ordering :=  transitive r ∧ asymmetric r 
def ordering :=         reflexive r ∧ transitive r ∧ anti_symmetric r
def partial_order :=    ordering r ∧ ¬ strongly_connected r
def total_order :=      ordering r ∧ strongly_connected r
def well_ordering :=    total_order r ∧ (∀ (s : set β),
                                           ∃ (b : β), 
                                             (∀ (b' : β), 
                                               b' ∈ s → 
                                               b ≺ b'))

end relation
end relations
