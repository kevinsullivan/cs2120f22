/-
Prove 0 ≠ 1.
-/

example : 0 ≠ 1 :=
begin
  assume h,
  cases h,    -- false is true in all (zero) cases!
end

example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f := h (eq.refl 0),
  contradiction,
end

/-
-/
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P p,
  assume h,
  contradiction,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/


/-
With the law of the excluded middle we can prove
that (double) negation elimination is a logically
valid form of reasoning. Without em, we're stuck.
-/
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P h,
  have pornp := em P,
  cases pornp with p np,
  exact p,                  -- case 1: assumption
  exact false.elim (h np),  -- case 2: contradiction
end

-- using assumption and contradiction tactics
example : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P h,
  -- stuck!
  have pornp := em P,
  cases pornp with p np,
  assumption,
  contradiction,
end



theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  split,        -- applies iff.intro
  -- forward
    assume h,

    -- case analysis on P being either true or false 
    cases (em P) with p np,

    -- P true
      -- case analysis on Q being either true or false
      
      cases (em Q) with q nq,

        -- P true, Q true
        -- trick: see and use the contradiction!
        exact false.elim (h (and.intro p q)),

        -- P true, Q false
        exact or.inr nq,

    -- P is false (no need for case analysis on Q)
    exact or.inl np,

  -- backwards: 
    intro h,
    cases h,
    assume k,
    exact h k.left,
    intro k,
    exact h k.right,
end

theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q h,
  cases (em P) with p np,

  -- case: P is true
  -- see opporunity to establish contradiction
  apply false.elim (h (or.inl p)),

  -- case: P is false
  apply and.intro np _,
  assume q,
  apply h (or.inr q),
end

theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  intros P Q,
  split,
  -- forward
  assume h,
  cases h with l r,
    -- left  
    exact or.inl l,
    -- right
    cases r with np q,
    exact or.inr q,
  -- backward
  assume h,
  cases h with p q,
  exact or.inl p,
  cases (em P) with p np,
  exact or.inl p,
  exact or.inr (and.intro np q),
end

theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  split,

  -- forward
  assume h,
  cases h with pq pr, -- ah ha, use cases here, too
  cases pq with p q,
  exact or.inl p,
  cases pr with p r,
  apply or.inl p,
  apply or.inr (and.intro q r),

  -- backward
  assume h,
  cases h with p qr,
  apply and.intro,
  exact or.inl p,
  exact or.inl p,
  cases qr with q r,
  apply and.intro,
  exact or.inr q,
  exact or.inr r,
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  split,
  -- forward
  assume h,
  cases h with pq rs,
  cases pq with p q,
  cases rs with r s,
  exact or.inl (and.intro p r),
  apply or.inr,
  exact or.inl (and.intro p s),
  cases rs with r s,
  apply or.inr,
  apply or.inr,
  exact or.inl (and.intro q r),
  apply or.inr, apply or.inr, apply or.inr,
  exact and.intro q s,
  -- backward

  -- Amanda and Ben, please finish this off
  admit,
end


/-
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ¬ (∀ (n : ℕ), n = 0) :=
begin
  assume h,
  have x := h 5,  -- any number other than 0 works here
  cases x,
end 

-- equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  split,        -- apply iff.intro _ _,
  
  -- forward
  cases (em P) with p np,
    -- P true
    assume h,
    apply or.inr,
    exact h p,
    assume h,
    -- P false
    exact or.inl np,

  -- backward
  assume h,
  cases (em Q) with q nq,
  assume p,
  assumption,       -- exact q
  assume p,
  cases h,          -- apply or.elim then assumes
  contradiction,
  contradiction,
end

example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  intros P Q h nq,
  cases (em P) with p np,
  have q := h p,
  contradiction,
  assumption,
end

example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q h,
  cases (em P) with p np,
  assume q,
  assumption,
  assume q,
  have nq := h np,
  contradiction,
end

