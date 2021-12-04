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

  -- unfold the definition of conjecture
  unfold conjecture,

  -- assume we're given an arbitrary but specific n
  assume n,
  
  -- unfold the definition of the property, P
  unfold P,

  -- the remainder of the proof is by induction on n

  -- proof by induction on n
  induction n with n' ih_n',
      -- n' is any natural number
      -- ih_n' is proof of (P n')

  -- base case: proof of (P 0)
  -- be sure you see why rfl is correct here
  apply rfl,

  -- step: proof of (∀ n', P n' → P (n'+1))
  -- Note that Lean already "assumed" n' and ih_n'
  -- leaving us to produce a proof of P (n'+1).

  /- 
  First, we will use the definition of sum_to 
  to simplify the statement of the goal. To help
  you remember, here's the definition of sum_to.
  The key observation now is that it gives you
  two equality axioms that you can now use. The
  first says sum_to nat.zero can be rewritten 
  to nat.zero. The second says that sum_to (n'+1)
  can be rewritten as sum_to n' + (n' + 1). These
  are not just rules for computing but they are
  also axioms we are given "by the definition of
  sum_to."
  
    def sum_to : ℕ → ℕ 
    | (nat.zero)    := nat.zero 
    | (n' + 1)  := (sum_to n') + (n' + 1)
  -/

  /-
  In English, our first step in proving the
  remaining goal is to simplify sum_to (n'+1)
  to (sum_to n') + (n' + 1) using the rules
  provided by the definition of sum_to. It's
  the second one that Lean will choose to use
  in the current proof state (as you would as
  well if you were doing all of this by hand).
  -/
  simp [sum_to],   
  /-
  Move your cursor back and forth between the
  proof state before you simplify and the state
  after, and understand the sense in which Lean
  is using one of the "computing rules" for the
  sum_to function as a *rewrite* rule that we 
  can and now have used in our proof.
  -/

  /-
  Here we reach a point of highest challenge. 
  The trick is to find a way to rewrite the
  goal, changing its form but not its meaning,
  so that in its new form we can finally use
  the induction hypothesis (which provides an
  answer for n') to rewrite the current goal
  into a form in which all the rest is basic
  algebra. 

  As we see now, rewriting by distributing 
  multiplication over addition "surfaces"
  a subterm of the form (P n'), for which 
  we've assumed we have a proof. 
  -/
  
  -- rewrite using right distributivity
  -- a * (b + c) = a * b + a * c
  -- mul_add is a theorem from Lean's libraries
  rw mul_add, 

  /-
  The key is to use rewriting to replace (P n')
  where it appears in the goal with the *answer*
  (result, proof) for n', which is exactly what is
  given by the induction hypothesis.
  -/

  -- rewrite using induction hypothesis
  -- 2 * sum_to n' = n' * (n' + 1)
  rw ih_n',   

  /-
  The rest of the proof is by basic algebra,
  -/

  /-
  First, as kind of a detail, we need to replace
  n'.succ with the equivalent, (n' + 1), where 
  the former appears in the goal. This involves
  rewriting the goal using a theorem proved in
  Lean's standard library. We just give you the
  name of this theorem/proof for free. Our main
  underlying aim here is to get the goal to be
  stated entirely in terms of + and * operations
  so that we can get proofs of equalities just
  by invoking a "ring equality solver." That is
  what the ring tactic is: if there's a proof it
  tries to find it for you. Again, our use of 
  the ring tactic here gives you a glimpse of
  the real power of automated proof assistants.
  -/
  
  -- rewrite succ as + 1 (to enable us of ring)
  -- n.succ = n + 1
  rw nat.succ_eq_add_one,

  -- the rest is simple algebra in a ring (a 
  -- set, here nat, with + and * operations
  -- that follow "usual" rules of arithmetic
  ring,    
end




-- WHY DOES SUCH A PROOF MATTER?

/-
Why might such a proof matter in practical
programming? Well, now you know that for any
natural number, n, you can compute the sum
of all the numbers from 0 to n without having
to "loop" n times to get an answer! Instead
you can just compute n*(n+1)/2. You thus have
a proof that justifies using the efficient 
formula n*(n+1)/2 instead of an interative
algorithm that takes as many steps as n is
big to compute an answer. You've proved that
there is a better algorithm for computing the
function as we defined it using recursion.
-/

def sum_to_optimized (n : ℕ) := n * (n + 1) / 2

/-
One important application of theorem proving in
computer science is just so to justify this kind 
of optimization. One place where optimizations are 
especially important is in compilers, which turn 
source code into bytecode or assembly code. A
compiler writers should always have a proof that
an optimzation that transforms either source code
to optimized source code, or assumbly code to 
optimized assembly code, doesn't thereby change
what the code computes. 

Tremendous gains in computer performance are due
not only to hardware getting faster but also to
improvements in software, including ones based on
compiler optimiztions.   
-/

