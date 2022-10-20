/-

-/

#check @or.elim

example : ∀ (P Q R: Prop), P ∨ Q → R :=
begin
  assume P Q R,     -- forall introduction
  assume h : P ∨ Q,
  apply or.elim h _ _,
  assume P,
   -- end of example,
end

example : ∀ (P Q R: Prop), P ∨ Q → ((P → R) → (Q → R) → R) :=
begin
assume P Q R,     -- forall introduction, assume PQR, show rest
assume (h : P ∨ Q),         -- arrow introduction
apply or.elim h,  -- or elimination (cases)

-- First case: assume P
assume (p : P),   -- arrow intro
assume pr,        -- arrow intro
assume qr,        -- arrow intro
exact (pr p),     -- arrow elimination

-- Second case: assuming Q is true
assume q pr qr,   
exact (qr q),
end

#check @or.inl
#check @or.inr

-- What does unfold do

def x := 0 = 1

def m := ∀ P, P ∨ ¬P

theorem foo : m  :=
begin
unfold m,
-- quit
end

-- What about iff

example : ∀ (P Q : Prop), P ↔ Q :=
begin
assume P Q,
apply iff.intro,
end 

variables (P Q : Prop)
variables (pq : P → Q) (qp : Q → P)

-- what I want is a proof that P ↔ Q

/-
We prove P ↔ Q from P → Q and Q → P by iff introduction
-/
example : P ↔ Q := (iff.intro pq qp)

variable piffq : P ↔ Q

example : P → Q := iff.mp piffq   -- weird name for elim_left (modus ponens)
example : Q → P := iff.mpr piffq   -- weird name for elim_right (modus ponens reverse)
-- don't worry about these details

theorem my_and_elim : ∀ (P Q), P ∧ Q → P :=
begin
  assume P Q,
  assume (pq : P ∧ Q),
  apply and.elim_left pq,
end 


