
/-
Remember: A predicate is a proposition with
one or more parameters. A simple example of
a predicate with one parameter (or argument)
is *evenness* of a natural number. Let's call
it ev. Then ev takes a single natural number
as an argument and returns the proposition
that *that* number is even (e.g., that the
number, n, mod 2, is 0).
-/
def ev (n : ℕ) : Prop := n % 2=0


/-
The introduction rule for exists takes two
arguments: a witness value, w, and a proof
that that witness satisfies the predicate. 
-/
example : ∃ (n : ℕ), ev n :=
begin
  /-
  It's often clear and useful to apply the
  introduction rule to a witness, leaving the
  proof that it satisfies the predicate to a
  separate sub-goal/sub-task. Notice how the
  value of the parameter is incorporated into
  the final proposition to be proved: that 
  that value has the required property.

  -/
  apply exists.intro 4 _, -- proof of ev 2 tbd
  --unfold ev,            -- remind me what ev 2 means
  exact rfl,
end

/-
The point of the next exampe is simply to
show notation you can use to specify the 
"dependently type pairs" that constitute
proofs of existential propositions. The
left and right angle brackets are special
characters in Lean by backslash less-than
and backslash greater-than characters.
-/
example : ∃ (n : ℕ), ev n := 
  ⟨ 2, rfl ⟩  -- notation


/-
Just as with ∀ quantifiers, which allow us to
say ∀ x, ∀ y, ∀ z, P x y z as ∀ (x y z), P x y z,
so we can write ∃ x, ∃ y, ∃ z, P x y z, with just
one ∃: ∃ x y z, P x y z. But the nice notation
hides a little bit of insight, which is that 
you do actually need to apply exists.intro to
produce three different proofs here, one for 
each ∃. Each application introduces on of the
witness/argument values. Watch carefully what
happens in the context as you move through the
steps of this proof.
-/
example : ∃ (a b c : ℕ), a*a + b*b = c*c := 
begin
  apply exists.intro 3 _,
  apply exists.intro 4 _,
  apply exists.intro 5 _,
  exact rfl, 
end

/-
Now consider a predicate with three arguments:
the predicate that expresses the property of
three natural numbers forming a Pythagorean 
triple, (a, b, c), with a * a + b * b = c * c.
-/
def pythagorean_triple (a b c : ℕ) : Prop :=
 a*a + b*b = c*c


/-
Let's demand a proof of the proposition that
(3, 4, 5) is a Pythagorean triple.
-/
example : pythagorean_triple 3 4 5 := 
begin
  --unfold pythagorean_triple, -- expand proposition to prove
  apply rfl,
end

/-
Is it true that for any natural number, n, there
is some natural number m, such that n = 2 * m? If
so, explain in English why there is. It might help
to complete the following formal proof. If not, say
why, briefly, giving a *counterexample* as proof
that the proposition is not true.
-/
example : ∀ (n : ℕ), ∃ (m : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro _,
  -- stuck
end

/-
On the other hand, is it true that for any natural
number m, there exists a natural number n that is
twice m? Yeah? For a given m, what number is it?
Why, it's just 2*m. That was easy.
-/
example : ∀ (m : ℕ), ∃ (n : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro (2*m) _,
  apply rfl,
  -- yay
end

