import tactic.ring
import tactic.norm_num

namespace cs2120f22

/-
We now launch into the final major topic of this
course: induction principles and how they enable
both the definition of recursive functions and
the construction of proofs "by induction." 
-/

/-
Key ideas #1: 

Every inductively defined data type comes with 
its own induction axiom. If you learned about
"proof by mathematical induction" in high school
or another course, you were learning how to use
the induction axiom for *natural numbers*, but
you can also use induction to reason about all
values of *any* inductively defined data type.

#2: If a type is named T, then T.rec_on is the 
name of the corresponding induction axiom *in 
Lean*. The idea of induction axioms is general,
but this is its implementation in Lean.

#3. An induction axiom is an axiom for proving 
*universal generalizations* (∀ propositions) 
that assert that something is true for *all* 
values of a given type.
-/

/-
As an example, let's look again at the definition
of the bool type, and then at its induction axiom.
-/

#check bool
/- 
inductive bool    -- data type definition
| ff : bool       -- first constructor
| tt : bool       -- second constructor
-/

#check @bool.rec_on
/-
bool.rec_on : 
  Π {motive : bool → Sort u_1} 
  (n : bool), 
  motive ff → motive tt → motive n

Let's decode that:
(0) bool.rec_on is an axiom that says that:
(1) for any property or function taking a bool
(2) and for any arbitrary Boolean value n
(3) if you prove that ff has the property
(4) and you prove that tt has the property
(5) then you've proved that any bool n has it.
-/

/-
Key idea #4: For simple types like bool whose
values are just "enumerated," proof by induction
amounts to proof by case analysis. As a reminder
of that strategy, here's a proof that for any
bool, n, the negation of the negation of n is n.
The idea is just to show it's true for each of
the values individually. 
-/
example : ∀ (n : bool), bnot (bnot n) = n :=
begin
assume n,
cases n,
exact rfl,
exact rfl,
end 

/-
Here's a proof of the same proposition by the
application of the induction axiom for bool.
-/
example : ∀ (n : bool), bnot (bnot n) = n :=
begin
-- let n be an arbitrary bool avlue
assume n,

-- apply the induction principle
apply bool.rec_on n,
/-
Note that the first *explict* argument
to bool.rec on is an arbitrary bool. We
can thus apply the principle to n, in
which case the remaining things to be
proved are motive tt and motive ff, the
"motive" being the property that "bnot 
(bnot n) = n." That is, we must prove
this proposition first for n = f and 
then for n = ff
-/
exact rfl,  -- easy
exact rfl,  -- easy
-- QED
end  

/-
Another way to think about the induction
principle for bool is that it provides a
means for implementing functions that take
any natural number as input. Suppose we
want to define a function that takes any
bool argument and that returns 0 for ff
and 1 for tt. Let's build this function
by applying the induction principles to
two such machines.
-/

def answer_for_ff := 0
def answer_for_tt := 1

def bool_to_bit (b : bool) : nat := 
  bool.rec_on 
  b 
  answer_for_ff 
  answer_for_tt

-- Test cases. It works!
example : bool_to_bit ff = 0 := rfl
example : bool_to_bit tt = 1 := rfl
/-
Take-away #1: For an enumerated type, such
as bool, we can build a proof that all values
of this proof have a given property. We do
this by applying the induction axiom to two
smaller "machines" each of which gives a 
proof for the corresponding bool input value.
Such a proof is basically a function that takes 
any bool and returns a proof for that value.

Take-away #2: For an enumerated type, such
as boolol, we can also build a *function* that
takes any value of this type and returns a
corresponding result value. To build such 
a function, we apply the induction axiom
to the return values for each of the possible
argument values.  

In either case, we apply the induction axiom
to proofs/values for each possible argument
value to obtain a machine that when given any
argument value returns the correct corresponding
proof or function value.  
-/

/-
EXERCISE: (1) define a data type called
day, the values of which are the (names
of) the days of the week. (2) Define a 
function, next_day : day → day, that if
given a day returns the next day of the
week, and define prev_day : day → day, 
that when given a day returns the previous
day. (3) Give a proof *by induction* of
the proposition that for any day, today, 
the day after yesterday is again today.
-/


/-
We now turn to the more interesting case of
the definition of the ℕ data type and *its* 
corresponding induction principle.
-/

open nat 
/-
inductive nat       -- data type definition
| zero              -- zero is a value of this type
| succ (n : nat)    -- given n : ℕ, succ n is also a ℕ

This data type is defined truly inductively.
It provides a constructor for "laying down a
ground floor" and it provides a constructor
that, "when placed on any floor, n'"" builds 
the "next floor up," for n = (succ n').
-/

def z := zero             -- first constructor
def one := succ z         -- second
def two := succ (succ z)  -- second
def two' := succ one      -- second
def three := succ (two)   -- second
def four := succ (succ (succ (succ zero)))

/-
Okay, now that we've got the ℕ data type
defined, let's define some functions on 
this type to precisely mimic (you could
even say, "to specify") basic arithmetic
functions.
-/


/-
increment -- given n', return n = n' + 1
-/
def inc (n' : ℕ) : ℕ := succ n'

-- it works!
#eval inc three
example : inc three = four := rfl


/-
decrement 

We define this function by case analysis on
an argument, n. If n is zero, we return zero.
Otherwise, if n = (succ n') we return n'. This
is a beautifully simple example of how we can
use pattern matching to "destructure" n into
(succ n'), then returning n'.
-/
def dec : ℕ → ℕ
| zero := zero
| (succ n') := n'

#eval dec 4 
#eval dec 0 

/-
How about a function for adding two natural
numbers, n and m. Now we get to see recursion
in action! We define n + m  to be n in case
m is zero, and otherwise n + (m' + 1) to be
1 + (n + m'), where (n + m') is computed by 
a call to the same addition function!
-/

#check nat.add

def my_add : ℕ → ℕ → ℕ 
| n 0 := n
| n (succ m') := succ (my_add n m')

-- a few test cases -- seems to work!
example : my_add 5 0 = 5 := rfl
example : my_add 5 3 = 8 := rfl


/-
Just as our implementation of addition
uses succ to add 1 to n "m times", we
can implement multiplication by adding
n to itself m times.
-/
def my_mul : ℕ → ℕ → ℕ 
| n 0 := 0
| n (succ m') := my_add n (my_mul n m') 

-- test cases
example : my_mul 7 0 = 0 := rfl
example : my_mul 7 1 = 7 := rfl
example : my_mul 7 5 = 35 := rfl

/-
And exponentiation multiplies n by itself
m times.
-/
def my_exp : ℕ → ℕ → ℕ 
| n 0 := 1
| n (succ m') := my_mul n (my_exp n m') 

-- test cases
example : my_exp 2 0 = 1 := rfl
example : my_exp 2 1 = 2 := rfl
example : my_exp 2 4 = 16 := rfl

/-
So now we'll see how we can "build"
recursive functions by applying the
induction axiom for natural numbers
to "two smaller machines", one that
gives an answer for argument zero and
one that, if given n' and the answer
for n', combines them to produce the
answer for n = n'+1. It will be a
lot easier to see the idea in action
with a unary function, taking just
one natural number argument. For this
example, we'll pick the factorial
function. Here it is as we'd usually
define it in Lean.
-/
def factorial : ℕ → ℕ 
| nat.zero := 1
| (nat.succ n') := my_mul (succ n') (factorial n')
-- parenthesize constructor expressions

-- it works
example : factorial 0 = 1 := rfl
example : factorial 5 = 120 := rfl
example : factorial 6 = 720 := rfl

/-
Yeah, now for the fun part. We will first
build two "machines." The first gives the
answer for n = 0. The second, given n' and
the answer for n' returns the answer for 
n' + 1. For example, suppose you want to 
compute the answer for n = 6. It's easy 
to compute if you know n' = 5 and that the 
answer for factorial n' is 120. To get the
answer for n = n' + 1 = 6, you multiply 
(n' + 1) = (5 + 1) by the factorial of n',
which is 120, to get the answer, 720, for
n = n' + 1 = 6. With these two machines, y
should be able to compute the factorial of
n for any n: run the first machine to get 
the answer for n' = 0, then pass n' and 
the answer for n' to the second machine to
get the answer for 1, then repeat that as
many times as needed to get the answer for
whatever n you want!  
-/

-- a "machine" returns factorial 0 
def fac_zero := 1

/-
A machine that when given n' and factorial
n' returns factorial of n' + 1.
-/
def fac_step 
  (n' : nat)     -- what floor you're on
  (n'_fac : ℕ)   -- answer for that floor
  := (n'+1) * n'_fac

/-
Applying the "step" machine to 5 and the
factorial of 5 (120) should return the
factorial of 6. And it does. 
-/

example : fac_step 1 1 = 2 := rfl     -- fac 2
example : fac_step 5 120 = 720 := rfl -- fac 6



def factorial' (n : nat) : nat := 
  nat.rec_on 
    n         -- given arbitrary n
    fac_zero  -- given the answer for n = 0
    fac_step  -- given function for computing the next the given n and factorial n the answer for  factorial n+1


-- It works! Yay!
example : factorial' 0 = 1 := rfl
example : factorial' 1 = 1 := rfl
example : factorial' 2 = 2 := rfl
example : factorial' 3 = 6 := rfl
example : factorial' 4 = 24 := rfl
example : factorial' 5 = 120 := rfl


/-
Let's see again how this work in terms of
the induction axiom for natural numbers.
Here's the axiom again.

  Π {motive : ℕ → Sort u_1}
  (n : ℕ), 
  motive 0 → 
  (Π (n : ℕ), motive n → motive n.succ) → 
  motive n

(1) Sort u_1, the "return type", is ℕ
(2) The n here is the argument to factorial'
(3) motive 0 = factorial' 0 = fac_zero = 1
(4) now see how our step function works
    (a) (Π (n : ℕ), motive n → motive n.succ)
    (b) it takes n, a nat, and motive n = factorial n
    (c) and it returns motive n+1 = factorial n+1

Applying the induction axiom to these arguments
yields a machine that given n return motive n = 
factorial' n *for any n whatsoever*. In a sense,
the big machine iterates application of the step
function as many times as needed, starting with
the value for the base case, to produce the value
that is sought!

So now we see how to explain the induction
principle in English. To produce a function
that can return a value (or if the return type
is a proposition in Prop, a proof that that
proposition) for *any* n, all you need to 
provide are (1) a machine returning a proof
for the base case of n = zero, and a machine,
the "step" function, that when given n' and
the correct result for n', return the result
for n' + 1.

When it comes to proofs of propositions about
all natural numbers, what you need to provide
is a proof for 0 and a proof that for any n',
if there's a proof for n' then there's a proof
for n' + 1. You just need to define how to get
a proof for n' + 1 *given the assumption that
you know n' and have a proof for n'. That is
proof by induction for the natural numbers,
also sometimes called proof by "mathematical"
induction.

What's amazing is that this technique will 
work just as well for lists, trees, programs,
or any other inductively defined data types as
it does for nat (albeit with different smaller
machines that need to be defined).
-/

/-
EXERCISE: Define a function that sums up all
the natural numbers from 0 to any given natural
number, n.
-/

def sum_to : ℕ → ℕ 
| 0 := 0
| (succ n') := (succ n') + sum_to n'

example : sum_to 0 = 0 := rfl
example : sum_to 5 = 15 := rfl
example : sum_to 10 = 55 := rfl

/-
Formulate property that you will then want
to prove holds for all natural numbers.
-/

def sum_property (n : ℕ) := 2 * sum_to n =  n * (succ n)

/-
Prove that the property holds for 0
-/

lemma sum_zero : sum_property 0 := eq.refl 0 

/-
Prove that if it holds for n' then it holds for n'+1
-/

lemma sum_n' : 
  ∀ n', sum_property n' → sum_property (succ n') :=
begin
  unfold sum_property,
  assume n' ind_hyp,
  unfold sum_to,
  ring,
  rw ind_hyp,
  ring,
end


/-
Put the "small machines" together using induction axiom
-/
example : ∀ (n : ℕ), sum_property n :=
  λ n, 
    nat.rec_on    -- apply induction axiom
    n             -- arbitrary n
    sum_zero      -- proof of base case
    sum_n'        -- proof of step/inductive case
/-
And have now is a "big machine" that, given *any*
n (base case or otherwise), produces a proof that
that (arbitrary) n has the sum_property. This is
thus a proof that every natural number has that
property, which is what we wanted to prove. 
-/

/-
-/
example : ∀ (n : ℕ), sum_property n :=
begin
-- let n be an arbitrary natural number
assume n,

-- unfold definition of sum_property
unfold sum_property, 

-- the proof is by induction on n
induction n with n' pf_n',

-- constructing a proof for the base case is easy
-- rfl alone would do but let's go step bf step
{ 
  unfold sum_to, 
  exact rfl,
},

/-
Now we have tp provide a proof for the inductive 
case. The crucial thing to see here is that Lean
has already *assumed* that n' is a nat and that
you have a proof for n'. These are of course just
the "inputs" to the "inductve" machine. If it
isn't clear, look at the second line of the proof
of sum_n' above. Here, Lean is automating that 
step of the proof for you. Key idea: when doing
a proof by induction on a ℕ, in the second step
you *assume* you're given both n' and a proof for
n' (the "induction hypothesis"), and you have to
then construct a proof for n'+1. This is how it
works!
-/
{ 
  -- expand definitions: sum_property and sum_to
  unfold sum_to,
  -- normalize/simplify algebra (distributive law)
  ring,
  -- KEY! rewrite goal using induction hypothesis!
  rw pf_n',
  -- now just push through the rest of the algebra
  ring,
},
-- QED
end 

/-
EXERCISE: Look at our definition of my_add. What
it does is give you the axioms for addition! It
says for any n, adding n and zero is n, and that
adding n and (succ m) [the case where the second
argument, m', is greater than 0, reduces to "one 
more than adding n and m'. Sum of n and m' here
is assumed to be available, and in practice is 
computed by a recursive call to my_add.

So now suppose you want to prove that for any
n, my_add n 0 = n. This is super-easy because
it's just an axiom *by our definition* of my_add.
-/

example : ∀ n, my_add n 0 = n :=
begin
assume n,
unfold my_add,
end

/-
On the other hand, we have no axiom that tells
us that for any n, 0 + n = n. That, we will have
to prove by induction. This is an exercise that 
you will carry out by constructing the smaller
proofs separately then combining them using the
induction axiom for ℕ, and then by using the
induction tactic in Lean.
-/

/- A. 
Formally specify the *property* of a natural 
number that you will then want to assert holds
for all natural numbers. This will be a predicate
on a natural number, n. Call it left_zero_add.
-/

def left_zero_add (n) := 0 + n = n

/-
Now construct separate proofs that (a) 0 has
this property, (b) if arbitrary n' has it then
so does succ n', and (c) that by the induction
axiom *all* natural numbers therefore have this
property. Call your proofs left_zero_zero,
left_zero_add_n, with the complete proofs being
called left_zero and left_zero'. Note the extra 
"my" in the last name -- to avoid conflicts 
with a result already in the Lean library.
-/

-- base case
theorem left_zero_add_zero : left_zero_add 0 :=
begin
-- unfold the definition, then eq reflexivity 
unfold left_zero_add,
end

-- inductive case
theorem left_zero_add_n' : 
  ∀ n', 
    left_zero_add n' →
    left_zero_add (succ n') :=
begin
unfold left_zero_add,
assume n' ind_hyp,
rw<-ind_hyp,
ring,
end

-- The final proof
theorem left_zero : ∀ n, 0 + n = n :=
begin
assume n,
exact 
  nat.rec_on 
    n 
    left_zero_add_zero 
    left_zero_add_n',
end

end cs2120f22
