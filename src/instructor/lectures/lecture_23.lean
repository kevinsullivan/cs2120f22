import .lecture_21 

/-
ADDITIONAL PROPERTIES OF RELATIONS
-/

namespace relations

section relation

/-
Define relation, r, as two-place predicate on 
a type, β, with notation, x ≺ y, for (r x y). 
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  

-- special relations on an arbitrary type, α 
def empty_relation := λ a₁ a₂ : α, false
def full_relation := λ a₁ a₂ : α, true
def id_relation :=  λ a₁ a₂ : α, a₁ = a₂ 

-- Analog of the subset relation but now on binary relations
-- Note: subrelation is a binary relation on binary relations
def subrelation (q r : β → β → Prop) := ∀ ⦃x y⦄, q x y → r x y


/-
Commonly employed properties of relations
-/

def total := ∀ x y, x ≺ y ∨ y ≺ x
/-
Note: we will use "total" later to refer to a different
property of relations that also satisfy the constraints
needed to be "functions."  
-/

def anti_reflexive := ∀ x, ¬ x ≺ x
def irreflexive := anti_reflexive r -- sometimes used
def anti_symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x

-- Exercises:
/-
- Name a common anti_symmetric relation in arithmetic
- Name a common asymmetric relation in arithmetic
-/

example : reflexive r → ¬ asymmetric r := _   -- true?
example : ¬ reflexive r ↔ irreflexive r := _  -- true?

-- transitive closure

inductive tc {α : Type} (r : α → α → Prop) : α → α → Prop
| base  : ∀ a b, r a b → tc a b
| trans : ∀ a b c, tc a b → tc b c → tc a c

end relation
end relations
