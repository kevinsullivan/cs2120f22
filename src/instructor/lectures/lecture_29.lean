import .lecture_28
-- defines sum_up_to 

/-
To review, last time we ended by using
induction to define a function that sums
up the numbers from 0 to any natural number
given as an argument. 
-/

#reduce sum_up_to 5


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
  (n : ℕ),                      -- argument n
  
  motive 0 →                    -- proof or value for 0

  -- a function that turns a value n and a result for n into a result for n+1
  (Π (n : ℕ), motive n → motive n.succ) → 

  -- gives you a result (proof or value) for arbitrary argument value, n
  motive n


/-
To apply induction, we had to define what
we might think of a two machines: the first
provides a fixed answer for a base case,
here where the argument is zero; and the 
second, a machine that, when given any 
natural nunber, n', and an answer/proof
for n', produces an answer/proof for n =
n' + 1. These two machine suffice to give
on the power to construct an answer/proof
for any argument value, n. 
-/

-- Let's define a binary function by induction
/-
Addition of natural numbers takes two numbers
as arguments and produces a third as a result.
-/

def my_add : ℕ → ℕ → ℕ :=
begin
  assume n m,

  -- define function by induction on first argument (of type nat)
  apply nat.rec_on n,

  -- define machine #1 : for n = 0 return m
  exact m,

  -- define machine #2: given any n' and a result for n',  output n'+1 result                     -- n'
  assume n',                    -- given any n'
  assume answer_for_n',         -- and an answer for n'
  -- produce an answer for n' + 1
  exact nat.succ answer_for_n', -- the result for n'+1

  /-
  That's it to the induction operation you provide the two machines,
  one a constant for a base case and one a function for building a 
  result for the next bigger argument value given the current argument
  value and an answer, computed so far, for that value.
  -/
end

#eval my_add 0 5
#eval my_add 1 5
#eval my_add 2 5
#eval my_add 3 5
#eval my_add 4 5
#eval my_add 5 5

/-
Programming is different than proving because when
proving, the details of a proof are irreleant: all
proofs are equally good (and indeed they're defined
to be equal), whereas when computing the details of
the derivation matter greatly. Here for example we
had to pick the right value for the base case and
the right method for deriving an answer for n'+1
from the values of n' and the answer for n'.
-/

/-
Here's exactly the same function defined using
Lean's more convenient "by cases" notation for
defining functions by giving answers for each 
of some number of possible cases for the inputs.
-/

def my_add' : ℕ → ℕ → ℕ 
| (nat.zero) m    := m
| (nat.succ n') m := nat.succ (my_add' n' m)

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
The difference between case analysis and
induction is that in the inductive case we
can assume that we have an answer (value or
proof) for n', and all we need to give is a
way to construct a proof/result for n' + 1.

The "answers" in turn now serve as additional
axioms that we can use in reasoning. For example,
we can see from the first rule that for any m,
0 + m = m, and it's easy to prove formally.
-/

example : ∀ (m : ℕ), my_add' 0 m = m :=
begin
  assume m,
  simp [my_add'], -- simplify using rules in definition
end

example : ∀ (m : ℕ), my_add' m 0 = m :=
begin
  assume m,
  -- apply rfl,       -- no rule for adding 0 on right!
  --simp [my_add'],   -- no rule for adding 0 on right!
  -- STUCK!
  -- ... or are we?!
end

/-
The conjecture is true. There is a proof by induction.
-/

example : ∀ (m : ℕ), my_add' m 0 = m :=
begin
    -- We define the big machine to take any m
    assume m,

    -- and to return a value computed by induction 
    apply nat.rec_on m,

    -- the machine answers for the base case, m = 0
    exact rfl,

    -- the second machine is a function that takes
    -- any n' and an answer for n' and that returns
    -- an answer for n'+1 
    assume n',        -- n'
    assume ih,        -- answer/result for n'
    -- simplify goal using rules defined in my_add'
    simp [my_add'],
    assumption,

    /-
    Having defined both machines required by nat
    induction and applied the induction axiom to
    these machines as arguments we produce a 
    machine that returns a result for *any* n:
    the base return value for the base case or
    by applying the induction function n times
    starting with 0.
    -/
end


/-
A little bit of Lean. Lean provides an "induction" tactic. 
When applied to a proof or value, the tactic provides proper
name for the cases, applies the appropriate induction axiom 
for the given type of value being "analyzed" (thank you, 
Jerimy Avigad for that word), and adds n' and the answer 
for n' as assumptions in the inductive case, leaving you to
define how you get from there to a proof/value for n=n'+1.
-/

example : ∀ (n : ℕ), my_add' n 0 = n :=
begin
    assume n,
    induction n with n' ih,

    -- base case, m = 0
    exact rfl,

    -- now we can simplify using the second rule
    simp [my_add'],
    -- my_add' n'.succ 0 = n'.succ
    -- succ (my_add' n' 0) = succ n'
    -- constructors are injective!
    -- my_add' n' 0 = n'

    -- rewrite goal using induction hypothesis
    exact ih,
end