/-*** example ***-/

/-
The "example" keyword specifies a type (often a proposition), and expects you 
to give a value of this type (often a proof), which it then *typechecks* for 
correctness. The only difference between example and def is that example does
not bind a given value to a variable. It typechecks it to make sure it's ok, 
and then just forgets about it. It's useful for checking that a proof is correct
without "remembering" the proof value by binding it to a variable. 
-/

def eight : ℕ := 8    -- typechecks 8 to ensure it's ℕ, binds value to "eight"
example : ℕ := 9      -- typechecks 9 to ensure it's ℕ and then forgets about it
example : ℕ := "Hi"   -- type error
example : true := true.intro -- checks that true.intro is a correct proof of true
example : ∀ (P Q : Prop), P ∧ Q → P := begin intros P Q h, exact and.elim_left h end  -- good proof
example : ∀ (P Q : Prop), P ∧ Q → P := begin intros P Q h, exact and.elim_right h end -- bad proof


