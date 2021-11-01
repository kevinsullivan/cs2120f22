import .lecture_21 

/-
ADDITIONAL PROPERTIES OF RELATIONS
-/

namespace relations

section relation

/-
Relation, r, as two-place predicate on (pairs of)
objects of a type, β, with infix notation, x ≺ y,
for (r x y). 
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  

def empty_relation := λ a₁ a₂ : α, false
def full_relation := λ a₁ a₂ : α, true
def id_relation :=  λ a₁ a₂ : α, a₁ = a₂ 




def total := ∀ x y, x ≺ y ∨ y ≺ x

--
def irreflexive := ∀ x, ¬ x ≺ x

--
def anti_symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y

-- "strictly anti-symmetric" above?
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x  

--
def empty_relation := λ a₁ a₂ : α, false

def subrelation (q r : β → β → Prop) := ∀ ⦃x y⦄, q x y → r x y

inductive tc {α : Type} (r : α → α → Prop) : α → α → Prop
| base  : ∀ a b, r a b → tc a b
| trans : ∀ a b c, tc a b → tc b c → tc a c


/-
-/

def identity_relation {α : Type} : α → α → Prop := λ a₁ a₂ : α, a₁ = a₂

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


def quasiordering := reflexive r ∧ transitive r
def strict_ordering := anti_symmetric r ∧ transitive r
def near_ordering := irreflexive r ∧ transitive r
def ordering :=      reflexive r ∧ anti_symmetric r ∧ transitive r -- new
def partial_order := reflexive r ∧ anti_symmetric r ∧ transitive r
def tolerance := reflexive r ∧ symmetric r


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