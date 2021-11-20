import .lecture_28
-- defines sum_up_to 

/-
To review, last time we ended applying induction
to define two fundamental total functions, from 
ℕ to ℕ. The first returns the sum of all of the
natural numbers from zero to any natural number,
n. The second returns the product of all of the
numbers from 1 up to any natural number, n, also
known as the factorial of n.
-/

#reduce sum_up_to 5
#reduce fac 5

/-
I'm going to tell two stories, and then
explain why they're two applications of
the same "polymorphic induction axiom."

First, we want a machine that, for any 
natural number, n, returns a proof that
n has some specific property, P.

Second, we want a machine that, for 
any natural number, n, returns the value
of a specific function, (P n). 

The difference is the first returns a 
proof of a proposition, P n, about n, while
the second returns the value of a function,
P n.

The key idea is that we can build each 
of these machines using the induction axiom
for the type of n. 

The induction principle is a machine that
takes two smaller machines as inputs and 
yields the machine that we want: the one
that takes *any* natural number and gives
back either a proof or a data value for 
n.

THe first machine just returns a proof or
a value for 0. The second machine takes 
two inputs, any natural number, n', and
the answer (proof or value) for n', and
it computes/constructs the correct result
for n'+1.

Now when the big machine is given any 
value n, it runs the first machine to 
get an answer for 0, and then it runs
the second machine as many times as
needed to get and answer for n, using
the output of each use of machine two
as the input to its next invocation. In
practice it usually involves counting
down from n to 0 rather than 0 up to n.

When you do a "proof by induction" what
you have to provide are the two smaller
machines! That's what proof by induction
does: it transforms the goal of proving
∀ n, P n, into two goals: one machine
that provides an answer for zero, and 
a second one, a *function*, that takes
any natural number, n', and the answer
for n', and computes a proof or value
for n'+1. With these machines in hand,
you can now apply proof by application
of the induction axiom for the given
type to get a machine that returns the
right result *for any* (∀) nat value,
n.
-/

#check @nat.rec_on

universe u_1
def induction_axiom_for_nat := 
Π                               -- for any
  {motive : ℕ → Sort u_1}       -- property or function of n
  (n : ℕ),                      -- and for *any* argument value n
  
  motive 0 →      -- if we have an answer for 0, and ...

  -- we have a "machine" turns any n' and the result for n' into a result 
  -- for n'+1
  (Π (n : ℕ), motive n → motive n.succ) → 

  -- Lean binds the unbound variable n instead of n' here; if it helps you
  -- can comment out this line and uncomment the next; they mean the same.
  --(Π (n' : ℕ), motive n' → motive n'.succ) → 

  -- then we can get an answer for any natural number n 
  motive n


/-
Before turning to the use of induction to construct proofs 
of the form, (∀ n, P n), we'll look at one more example of
its use to construct arithemtic functions, In this case we
will define natural number addition, a binary operation, of
type ℕ → ℕ → ℕ, "by induction" on one of the two arguments.
-/

-- Let's use our familiar proof-building tactic language 
/-
Addition of natural numbers takes two numbers
as arguments and produces a third as a result.
-/
def my_add : ℕ → ℕ → ℕ :=
begin
  -- assume values for arguments, n and m
  assume n m,

  -- define function by induction on n
  induction n with n' answer_for_n',

  -- define machine #1 : for n = 0 return m
  -- why? we're saying 0 + m = m for any m
  exact m,

  /- machine #2: given any n' and a result 
  for n' return the result for n'+1. A result
  for n' answers the question what is n' + m.
  What is the answer for n'+1, well that is
  just the successor of the answer for n'. 
  -/
  exact nat.succ answer_for_n', -- the result for n'+1

/-
Having successfully provided the arguments required
by induction on the natural numbers, you now have a
total function, from any natural number to its value
as transformed by that function.
-/
end

#eval my_add 0 5
#eval my_add 1 5
#eval my_add 2 5
#eval my_add 3 5
#eval my_add 4 5
#eval my_add 5 5
#eval my_add 1000 1234


/-
PROOF IRRELEVANCE VS PROGRAMMING
-/

/-
Programming is different than proving because when
proving, the details of a proof are irreleant: all
proofs are equally good (and indeed they're defined
to be equal in the logic of Lean). By contrast, when
computing, the specific "proof" matters greatly. As
an example, our functions, sum_to and factorial both
"prove the type, nat → nat," but here in the realm
of computing, we care which one we use! 
-/

/-
Here's exactly the same function defined using
Lean's more convenient "by cases" notation.
-/

def my_add' : ℕ → ℕ → ℕ 
| (nat.zero) m    := m
| (nat.succ n') m := nat.succ (my_add' n' m)
--                           ^answer for n'^

#eval my_add' 0 5
#eval my_add' 1 5
#eval my_add' 2 5
#eval my_add' 3 5
#eval my_add' 4 5
#eval my_add' 5 5

/-
EXERCISE: Write the factorial function using this
convenient notation.
-/

/-
EXERCISE: Now that you have a function for adding
two natural numbers, using induction to define a
function that derives the product of any pair of
natural numbers.
-/

/-
PROVING THEOREMS BY INDUCTION
-/

/-
The difference between simple case analysis and
induction is that induction let's us assume we 
are given an arbitrary number, n', and an answer
(value or proof) for n'. Have these objects is 
often the key to completing a proof,by giving a
formula that uses them to computing a result 
n'+1. 

Now we'll show where case analysis suffices to
prove that 0 is a left identity for addition as
we've defined it (because we've given the rule
for this case to the induction operation), but
where it will not work to prove that 0 is a 
right identity, For that, we'll need, and we'll
demonstrate, proof by induction.
-/

/-
An easy proof that 0 is a left identity.
-/

example : ∀ (m : ℕ), my_add 0 m = m :=
begin
  assume m,
  apply rfl, 
end

/-
Why does case analysis fail in a proof that it's
also a right identity? Because we don't already
have a rule for that, as we did for the left case.
-/
example : ∀ (m : ℕ), my_add m 0 = m :=
begin
  assume m,
  apply rfl,          -- no rule for adding 0 on right!
  -- STUCK!
end

/-
... or are we?!

Froof by induction on m. It will suffice
to specify a result when m is zero, and a
result for any number, n'+1, when given n'
and the result for n'. 
-/

#reduce my_add

/-
Let's start by checking out my_add in
more detail
-/
#check my_add
#reduce my_add
/-
λ (n m : ℕ), 
  nat.rec 
    m       -- value for base case n = 0
            -- computation for n'+1 from n'
    (λ (n' answer_for_n' : ℕ), answer_for_n'.succ) 
    n       -- 
-/
#check @nat.rec
/-
nat.rec :
Π 
  {motive : ℕ → Sort u_1}, 
  motive 0 →            -- answer for base case 
  (Π (n : ℕ),           -- next answer generator
     motive n → 
     motive n.succ) →   
  Π (n : ℕ), motive n   -- answer for any n
-/



example : ∀ (n : ℕ), my_add n 0 = n :=
begin
    assume n,
    induction n with n' ih,

/-
Π 
  {motive : ℕ → Sort u_1}, 
  motive 0 → 
  (Π (n : ℕ), motive n → motive n.succ) → 
  Π (n : ℕ), 
  motive n
-/

    -- base case, n = 0
    --simp [my_add],
    exact rfl,

    -- inductive 
    -- simplify using rules that define my_add
    -- my_add n'.succ 0 = n'.succ
    -- succ (my_add n' 0) = n'.succ
    simp [my_add],
    /-
   Sullivan working to reduce unnecessary
   complexity in proof state as expressed.
    -/
    -- nat.rec 
      -- 0 
      -- (λ (n' : ℕ), nat.succ) 
      -- n'
    /-
    Application to n' of function
    defined by induction where (1)
    answer for 0 is 0, and (2) the
    answer for n'+1 is generated by
    succ, applied to n' is n'. But
    that's the induction hypothesis. 
    -/
    exact ih,
end

example : ∀ (n : ℕ), my_add n 0 = n :=
begin
    assume n,
    apply nat.rec_on n,

/-
Π 
  {motive : ℕ → Sort u_1}, 
  motive 0 → 
  (Π (n : ℕ), motive n → motive n.succ) → 
  Π (n : ℕ), 
  motive n
-/

    -- base case, n = 0
    --simp [my_add],
    exact rfl,

    -- inductive  case

    -- two arguments
      -- n'
      -- result for n'
    -- produce result for n'+1

    assume n' ih,

    /- 
    simplify application of my_add
    and further simplify resulting
    expression.
    -/
    simp [my_add],
    /-
    We will better explain what happens
    here and what the resulting goal is
    actually saying. REST IS STILL WORK
    IN PROGRESS.
    -/
    
    /- 
    (nat.rec 
      0 
      (λ (n' : ℕ), nat.succ)
    ) 
    n'
    -/

    /-
    Application to n' of function
    defined by induction where (1)
    answer for 0 is 0, and (2) the
    answer for n'+1 is generated by
    succ, applied to n' returns n'. 
    -/

    -- Simplify by definition of my_add
    -- in expression for induction hypothesis
    simp [my_add] at ih,

    /-
    It's clear that we've defined our
    second "machine".
    -/
    assumption,
end
