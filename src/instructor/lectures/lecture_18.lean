import .lecture_17

/-
Now that we've seen how to formalize 
set theoretical concepts, such as the
intersection of sets, on a foundation
of logic, we can state and the prove
theorems about sets. Let's just make
some up. 
-/

theorem foo : ∀ (n: nat), ev n → od (n + 1) :=
begin
    assume n h,
    unfold ev at h,
    unfold od,
    assume k,
    unfold ev at k,
    rw <-k at h,
    induction n with n' ih,

    -- base case
    contradiction,
    
    -- inductive case
    -- ih says n%2 never equals (n+1)%2


end

theorem ev_or_od : ∀ n, ev n ∨ od n :=
begin
  assume n,
  
end

example : ∀ (n : ℕ), evens_union_ods n ↔ complete n := 
begin
  assume n,
  split,
  -- forward
  assume h,
  unfold complete,
  assume h,
  unfold evens_union_ods, 
  show (ev n ∨ od n),
  cases n,
  -- n zero
  apply or.inl,
  exact rfl,
-- n non-zero
  apply or.inl,

end


example : ∀ (n : ℕ), (n ∈ evens_union_ods) ↔ (n ∈ complete) := 
_


/-
Now we are in a position to see formal 
definitions of all of the preceding set
theory concepts.
-/

axioms (P Q : ℕ → Prop)

def pSet  : set nat := { n : ℕ | P n}
def qSet  : set nat := { n : ℕ | Q n}

#reduce 0 ∈ pSet
#reduce pSet ∪ qSet
#reduce pSet ∩ qSet
#reduce pSet \ qSet
#reduce pSet ⊆ qSet
#reduce 𝒫 pSet      -- harder to decipher


/-
Now that we understand these operations and
their corresponding notations in set theory,
we can start to state and prove theorems!
-/


