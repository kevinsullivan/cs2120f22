/-
Operations on relations
-/

/-
We now change our attention to binary relations
more generally: not just from β → β but between
different types, α and β. Not the change in the
type of r as defined here.
-/ 

variables (α β γ : Type) (r : α → β → Prop)
local infix `≺`:50 := r

-- inverse of r
def inverse : β → α → Prop :=
λ (b : β) (a : α), r a b


-- composition of s with r
def composition (s : β → γ → Prop) :=
  λ a c, (∃ b, s b c ∧ r a b)


-- image of a set, s, under r
def image (s : set α) : set β :=
{ b : β | ∃ a : α, r a b}


def inv_image (f : α → β) : β → α → Prop :=
λ a₁ a₂, f a₁ ≺ f a₂



lemma inv_image.trans (f : α → β) (h : transitive r) : transitive (inv_image r f) :=
λ (a₁ a₂ a₃ : α) (h₁ : inv_image r f a₁ a₂) (h₂ : inv_image r f a₂ a₃), h h₁ h₂

lemma inv_image.irreflexive (f : α → β) (h : irreflexive r) : irreflexive (inv_image r f) :=
λ (a : α) (h₁ : inv_image r f a a), h (f a) h₁



