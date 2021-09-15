/-
DEFINITION
-/

def x : ℕ := 7
example : ℕ := 5

/-
PROPOSITION

Any statement, claim, conjecture, that could have a truth value.
-/

def ev (n : ℕ) := n % 2 = 0

/-
5 is even
-/

example : ℕ := 5

example : ev 5 := 
begin
  unfold ev,
  -- give up, i'm stuck
end

/-
4 is even
-/

example : ev 4 := 
begin
  unfold ev,
  exact (eq.refl 0),
end


/-
PREDICATE: 

- Proposition with parameters.
- A parameterized *family* of propositions
-/

-- def ev (n : ℕ) := n % 2 = 0


#reduce (ev 5)
#reduce (ev 4)
#reduce (ev 33)

/-
An axiom is a proposition whose
truth we just assume, without any
proof.
-/

def z := 
begin
  exact 4
end 

def id_nat (n : ℕ) := 
begin
  exact n,
end

#reduce id_nat 2

axiom equality_is_reflexive :
  ∀ (T : Type) (t : T), 
  t = t

#reduce equality_is_reflexive ℕ 3

def three_equals_three : 3 = 3 := (eq.refl 3)
def k : ℕ := 5

example : ∀ (T : Type) (x y z : T),
  x = y → y = z → x = z :=
begin
  assume T,
  assume x y z,
  assume h1,
  assume h2,
  rw h1,
  exact h2,
end

/-
Give an English language proof that
for any x and y, if x = y then y = x.

Proof: We'll assume we're given arbitrary
but specific values of x and y, and in this
context what remains to be proved is that
if x = y then y = x. To prove this we first
assume x = y, and in this context what now
remains to be proved is y = x. To prove that
y = x we can first apply the axiom of the
substitutablity of equals for equals to
rewrite y = x as y = y, justified by the
assume that x = y. So what now remains to 
be proved is that y = y, and this is true
by the application the axiom of reflexivity.
QED.

Proof. Rewrite y = x as y = y using substitutablity
of equals then apply the axiom of reflexivity
of equality. DONE.
-/

/-
Conjecture: There exist natural numbers, 
x, y, and z, all greater than 1, and n > 2,
such that x^n + y^n = z^n.  
-/