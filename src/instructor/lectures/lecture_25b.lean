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

end relation
end relations
