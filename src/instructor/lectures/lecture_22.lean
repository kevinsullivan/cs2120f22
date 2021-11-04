import tactic.ring

/-
State formally and prove the proposition
that congruence mod n is an equivalence
relation. Follow the steps below.
-/

/-
First, we need to define congruence mod n.
Technically it is defined not only on the
natural numbers but on the integers. 

Here's the English language definition:
Given a natural number, n, greater than 1 
(a "modulus"), two natural numbers, a and 
b, are "congruent modulo n", if n is a 
divisor of their difference: that is, if 
there is some natural number, k such that 
a − b = kn).

Your first task is to define cong_mod,
formally, stating that for any value, 
n, cong_mod n is a binary relation 
on natural numbers, as defined above.
-/

def cong_mod (n a b : ℤ) : Prop :=
  ∃ k, a - b = k * n

/-
Second, formally state the proposition that
for each natural number, n, "cong_mod n" is 
an equivalence relation. You should use the
"equivalence" predicate on binary relations
defined in Lean's library (which is the same
as our definition from the last lecture) in
writing this propopsition.
-/

def cong_mod_n_is_equiv_relation (n : ℤ) : Prop := 
  equivalence (cong_mod n) 

/-
Note that partial evaluation makes 
cong_mod n into a binary relation: in
that it's waiting for two more natural
number arguments, let's say, a and b,
and when applied to such arguments, 
it yields the proposition that the 
two numbers are congruent as defined.
-/

#reduce cong_mod (4:ℤ)
#reduce cong_mod (4:ℤ) (6:ℤ) (10:ℤ)

-- First, translate the goal into ordinary notation
-- Now what must you choose as a witness for a proof?


-- Let's 
example : cong_mod (4:ℤ) (6:ℤ) (14:ℤ) :=
begin
  unfold cong_mod,
  apply exists.intro (-2:ℤ),
  apply rfl,
end

/-
Now assert and prove this proposition to be
a theorem, i.e., to have a proof.
-/

example (n : ℤ) : cong_mod_n_is_equiv_relation n :=
begin
  unfold cong_mod_n_is_equiv_relation,
  unfold equivalence,
  split,  -- chooses to apply and.elim
  
  -- reflexive
  unfold reflexive,
  assume k,
  unfold cong_mod,
  apply exists.intro (0:ℤ),
  ring, 

  -- symmetric
  split,
  unfold symmetric cong_mod,
  assume x y h,
  cases h with v pf,
  apply exists.intro (-v),
  ring,
  rw <-pf,
  ring,

  -- transitive
     -- you prove it

  unfold transitive cong_mod,
  assume x y z h1 h2,
  cases h1 with h1v h1pf,
  cases h2 with h2v h2pf,
  apply exists.intro (h1v+h2v),
  rw int.distrib_right _ _ _,     -- LIBRARY LOOKUP!
  rw <-h2pf,
  rw <-h1pf,
  ring,
end

/-
A version of congruence mod n restricted to the
natural (non-negative whole) numbers.
-/

/-
Previous problem requires access to negative
numbers because it involves a term a-b, which,
in ℤ can be negative. If it's negative in ℤ it
will simply be truncated to 0 in ℕ, losing
critical information. 
-/

#reduce (6:ℤ) - (11:ℤ)
#reduce 6-10            -- oops
#reduce 6-11            -- oops
#reduce 6-12            -- oops


def cong_mod_nat (n a b : ℕ) :=
  a%n = b%n

example : cong_mod_nat 4 3 7 :=
begin
  unfold cong_mod_nat,
  exact rfl,
end

example (n : ℕ): equivalence (cong_mod_nat n) :=
begin
end