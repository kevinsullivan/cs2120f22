-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  trivial,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have zeqz := eq.refl 0,
  have f : false := h zeqz,
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  split,
  -- forward
  assume h,
  cases (classical.em P) with p np,
  cases (classical.em Q) with q nq,
  have pq := and.intro p q,
  contradiction,
  exact or.inr nq,
  exact or.inl np,
  -- backward
  admit,
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → (¬P ∧ ¬Q) :=
begin
  assume P Q,
  assume h,
  cases (classical.em P) with p np,
  cases (classical.em Q) with q nq,
  have porq := or.intro_left Q p,
  contradiction,
  have porq := or.intro_left Q p,
  contradiction,
  cases (classical.em Q) with q nq,

end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : _ :=
begin
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
end



axioms (T : Type) (Q : Prop) (f : ∀ (t : T), Q) (t : T)
example : Q := f t
#check f
