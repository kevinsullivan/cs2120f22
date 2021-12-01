import algebra.algebra.basic tactic.ring

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
We've already seen the definition of the nat type
and of the add function. Really undersatnding how
exactly they're defined is essential if one is to
gain a full understanding of our induction proof. 
-/

/-
With the nat type and the add function defined,

We define sum_to : ℕ to ℕ to be a function that
returns the sum of the natural numbers from 0 to
the argument, let's call it n. 
-/

def sum_to : ℕ → ℕ 
| (nat.zero)    := nat.zero                 -- base 
| (nat.succ n')  := (sum_to n') + (n'.succ) -- step

/-
We can test the function to see that it works.
(Note: we're using a logical proof as a test case).
-/

example : sum_to 5 = 15 := rfl
example : sum_to 10 = 55 := rfl


/-
Now we're ready. The first major step is to formally
state the *property* that every value of type nat is
claimed to have. For a given n, the proposition that
expresses the property is that sum_to n = n*(n+1)/2,
or, equivalently 2 * (sum_to n) = n*(n+1)/2. We write
the property formally by making n here into a general
argument value. 
-/

def P : ℕ → Prop := 
  λ n, 2 * sum_to n = n * (n + 1)

/-
Note that P has the type (ℕ → Prop) of any predicate
on (or property of) natural numbers, and we define it
in particular to be a function that takes any value,
n, of type nat, and that reduces to the proposition, 
2 * sum_to n  = n * (n + 1). 
-/

/-
Next we write the conjecture that we've set out to 
prove. It will be a universal generaliation of the
form, (∀ n, P n), that asserts that *every* value 
of the type of n has property P. In our case, it
asserts that for every nat, n, 2 * (sum_to n) = 
n*(n+1).
-/

def conjecture := ∀ n, P n 

/-
The "conclusion" of the induction rule (a chain
of implications) is exactly of this form, and its 
antecedents specify what values/proofs have to be
provided be provided for the rule to apply. We are
ready to exhibit a formal proof by induction of 
our conjecture. It's vitally important that you
work your way through this proof step by step,
carefully studying the proof context at each 
point in the proof to see how each inference
gets us closer to a complete proof.
-/

theorem sum_to_opt : conjecture := 
begin
  unfold conjecture,

  -- assume we're given an arbitrary but specific n
  assume n,
  
  -- expand the definition of P
  unfold P,

  
  -- proof by induction on n, where
      -- n' is index of ih_n'
      -- ih_n' is proof for n'
  induction n with n' ih_n',

  /-
  By induction, it will suffice to prove
  each of the subordinate lemmas: the base
  lemma, (P 0); and the step (inductive) 
  lemma, (∀ n', P n' → P (n'+1)),. When
  proved, the latter will enable us to
  construct a proof for n'+1 given a
  proof for n'. And if given a proof for
  0, then we'll be able to construct a
  proof for any n by applying the base
  lemma once and the step lemma n times.
  -/

  -- base machine: proof of (P 0)
  apply rfl,

  -- step machine: proof of (∀ n', P n' → P (n'+1))
  -- Note that Lean already "assumed" n' and ih_n'
  -- leaving us to show that from these assumed
  -- objects we can construct a proof of P (n'+1).

  /- 
  First, we have to use the definition of sum_to 
  to simplify the statement of the goal. To help
  you remember, here's the definition.
  
    def sum_to : ℕ → ℕ 
    | (nat.zero)    := nat.zero 
    | (n' + 1)  := (sum_to n') + (n' + 1)

  The following use of the simp (for simplify)
  tactic in Lean attempts to simplify the goal
  by rewriting it using equalities stipulated
  by the equalities used in the definition of
  sum_to. It uses the second rule to rewrite
  sum_to n'.succ as (sum_to n' + (n' + 1))
  -/
  simp [sum_to],   

  -- rewrite using right distributivity
  -- a * (b + c) = a * b + a * c
  -- mul_add is a theorem from Lean's libraries
  rw mul_add, 

  -- rewrite using induction hypothesis
  -- 2 * sum_to n' = n' * (n' + 1)
  rw ih_n',   

  -- rewrite succ as + 1 to enable ring reasoning
  -- n.succ = n + 1
  rw nat.succ_eq_add_one,

  -- finish off with basic algebra in a ring 
  -- set with + and * operators with usual laws
  ring,    

  -- QED       
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

def sum_to_optimized (n : ℕ) := n * (n + 1) / 2

/-
One important application of theorem proving in
computer science is precisely to justify this
kind of optimization of otherwise costly methods
of computing desired results. One place where
optimizations are often made is in the compilers
that turn our source code into bytecode or into
assembly code. Compiler writers have to *prove*
that optimizations don't change what a program
computes, only how efficiently it computes it. 
-/

