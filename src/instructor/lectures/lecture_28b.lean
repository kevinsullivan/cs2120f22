/-
We've now proved manually that the number of the
numbers from 0 to n is n(n+1)/2. In this file we
present the informal proof again, and then show
how to make its set-up precise in Lean.
-/

/-
Informal version.

Let's use (sum_to n) to denote the sum of the 
natural numbers from 0 to any natural number, 
n. Then the *property*, P(n) that we want to
show holds for of every natural number, n, is
that sum_to n = n(n+1)/2.

Theorem: ∀ n, P(n).

Proof: By induction applied to proofs of the 
two lemmas, P(0), and ∀ n', P(n') → P(n'+1). 

Lemma 1: P(0). Both sum_to 0 and 0(1)/2 equal
zero, and so are equal. 

Lemma 2: Assume n' is arbitrary and that we
know P(n') hols, that sum_to n' = n'(n'+1)/2.
We have to show sum_to (n'+1) = (n'+1)(n'+2)/2.

Observe that sum_to (n'+1) = sum_to n' + (n'+1).
Rewriting using our induction hypothesis we have
sum_to (n'+1) = n'(n'+1)/2 + (n'+1). Adding, we
have sum_to (n'+1) = (n'^2 + n')/2 + 2(n'+1)/2
= (n'^2 + n' + 2n' + 2)/2 = (n'+1)((n'+1)+1)/2.

We've thus shown that if P holds for n' then it
holds for (n'+1). With this case and the base 
case proved, we apply induction to get our final
result, a proof of P(n) for arbitrary n, which
is to say, ∀ n, P n. QED.
-/

/-
Here's how we'd "line up" to formalize this proof
in Lean. As a first step, we actually defined the
sum_to function formally, so that we can define
P(n) formally.
-/

/-
We define sum_to : ℕ to ℕ to be a function that
returns the sum of the natural numbers from 0 to
the argument, let's call it n. 
-/

def sum_to : ℕ → ℕ 
| (nat.zero)    := nat.zero           -- base case
| (n' + 1)  := (sum_to n') + (n' + 1) -- recursion

/-
We can test the function to see that it works.
(Note: we're using a logical proof as a test case).
-/

example : sum_to 5 = 15 := rfl
example : sum_to 10 = 55 := rfl


/-
The property (P n) can be rewritten as follows, (by
multiplying both sides by 2) to avoid having to deal
with a division operation on the right hand side. Be
*sure* you understand what the lambda means in this
expression!
-/

def P : ℕ → Prop := λ n, 2 * sum_to n = n * (n + 1)

/-
Now the conjecture that we've set out to prove is
the usual, (∀ n, P n), which asserts that *every*
natural number has this property.
-/

def conjecture := ∀ n, P n 

/-
So let's start to take a look at proving our
conjecture by induction, without worrying about
formally proving the inductive case (for now).
-/

example : conjecture := 
begin
  unfold conjecture,
  unfold P,

  -- assume we're given an arbitrary but specific n
  assume n,

  -- proof by induction on n
  induction n with n' ih_n',

  /-
  Now we just need to provide the two "machines"
  that induction takes as arguments: one that gives
  a proof of (P 0) and one that gives a proof of 
  (∀ n', P n' → P (n'+1)), which is to say that if
  we know n' and have a proof of P n' then we can
  derive a proof of P (n'+1).
  -/

  -- machine #1, a proof of (P 0)
  apply rfl,

  -- machine #2, proof of (∀ n', P n' → P (n'+1))
  -- Note that Lean already "assumed" n' and ih_n'
  sorry,  -- we'll skip the algebra for now
end

-- WHY DOES ALL OF THIS MATTER?

/-
So why does all this matter to the practical
programmer? Well, now you know that for any
natural number, n, you can compute the sum
of all the numbers from 0 to n without having
to "loop" n times to get an answer. Instead
you can just compute n*(n+1)/2. You thus have
a proof that justifies using the efficient 
formula n*(n+1)/2 instead of an algorithm 
that takes time proportional to n to compute
the answer. You've proved that there is a
much better algorithm for computing this
function.
-/

def sum_to_optimized_version (n : ℕ) := n * (n+1) / 2

/-
One important application of theorem proving in
computer science is precisely to justify this
kind of optimization of otherwise costly methods
of computing desired results. One place where
optimizations are often made is in the compilers
that turn our source code into bytecode or into
assembly code. Compiler writers have to *prove*
that such optimizations don't change what a given
program computes, only how efficiently it can
compute it. 
-/