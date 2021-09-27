
/-
A simple predicate.
-/
def ev (n : ℕ) : Prop := n%2=0


/-
Introduction rule for exists
-/
example : exists (n : ℕ), ev n :=
begin
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