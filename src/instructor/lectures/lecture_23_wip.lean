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


inductive tc {α : Type} (r : α → α → Prop) : α → α → Prop
| base  : ∀ a b, r a b → tc a b
| trans : ∀ a b c, tc a b → tc b c → tc a c


/- 
Reflecting
https://dml.cz/bitstream/handle/10338.dmlcz/142762/ActaCarolinae_048-2007-1_5.pdf,
provide formal definition of each of the following properties of a binary relation, 
r, on objects of a type, β. We will call r 

– a quasiordering if r is reflexive and transitive;
– a strict (or sharp) ordering if r is irreflexive and transitive;
– a near-ordering if r is anti_symmetic and transitive;
– a (reflexive) ordering if r is reflexive, antisymmetric and transitive;
– a tolerance if r is reflexive and symmetric;
– * an equivalence if r is reflexive, symmetric and transitive
-/


def ordering := reflexive r ∧ transitive r ∧ anti_symmetric r -- new
def strict_ordering := asymmetric r ∧ transitive r
def partial_order := reflexive r ∧ anti_symmetric r ∧ transitive r ∧ ¬ total r
def total_order := reflexive r ∧ anti_symmetric r ∧ transitive r ∧ total r

/-
Definitions vary subtly. Be sure you know what is meant by these terms in any
given setting or application.
-/

end relation
end relations

/- 
Pullback from binary relation along function and properties it preserves,
straight from Lean 3 Community mathlib. 

def inv_image (f : α → β) : α → α → Prop :=
λ a₁ a₂, f a₁ ≺ f a₂

lemma inv_image.trans (f : α → β) (h : transitive r) : transitive (inv_image r f) :=
λ (a₁ a₂ a₃ : α) (h₁ : inv_image r f a₁ a₂) (h₂ : inv_image r f a₂ a₃), h h₁ h₂

lemma inv_image.irreflexive (f : α → β) (h : irreflexive r) : irreflexive (inv_image r f) :=
λ (a : α) (h₁ : inv_image r f a a), h (f a) h₁
-/