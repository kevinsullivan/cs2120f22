/-
We
-/

def ev (n : ℕ) : Prop := n%2=0

example : exists (n : ℕ), ev n :=
begin
  apply exists.intro _ _,
  exact 6,
  apply eq.refl,
end

example : exists n, ev n := _

example : exists (a b c : ℕ), a*a + b*c = c*c := 
_



example : ∃ (n : ℕ), (ev n → (∃ (m : ℕ), n = 2 * m)) :=
begin

end

example : ∀ (n : ℕ), (ev n → (∃ (m : ℕ), n = 2 * m)) :=
begin

end