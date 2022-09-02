/-
∀ x, x = x
-/

#check ∀ (T : Type) (x : T), x = x
#check ∀ (P : Prop), P ∨ ¬P
#check ∀ (P : Prop), ¬(P ∧ ¬P)

#check ∀ (X Y Z), (X ∧ Y) ∧ Z → X ∧ (Y ∧ Z)
#check ∀ (X Y Z), (X ∧ Y) ∧ Z ↔ X ∧ (Y ∧ Z)