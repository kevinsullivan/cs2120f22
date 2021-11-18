namespace hidden

/-
So far in this class, we've worked with just
a few types of data, mostly natural numbers,
though we've also seen that we have a Boolean
type (with values ff and tt) and a string type,
with values such as "" and "Hello, Logic!"

Today we're going to break some new ground with
the introduction of inductively defined types
and their corresponding induction axioms. These
new axioms, one per data type, will give us a
new way to construct proofs of properties *for
all* values of a given type, or to construct 
output results for functions that can take 
*any* value of a given type as an argument.
-/

/-

We will see not only that we can *define new
data types* of our own, but also that (1) we
can define the introduction rules for each
new type, in the form of a set of constructors,
which you use to *construct* value of a type; 
and (2) each such type comes with an axiom that
defined an elimination rule for that type that
we call an *induction* axiom or principle. 

This axiom enables you either (1) to construct 
a *logical proof* that, every value of the type
makes some proposition true (e.g., that every
value of a type has a given property); or (2)
to define a computational *function* that, for 
any argument value of the given type returns a 
correct value.
-/

/-
When we construct a proof using an induction 
principle we call it "proof by induction." When
we define a function using an induction principle
we (generally) call it a "recursive" function.
-/

/-
To help build an understanding of these ideas
based on what you already know, we'll look at
the induction principles, and how to use them
both to construct proofs and to define functions,
for the following five types:

empty   -- an uninhabited *data* type
unit    -- a data type with one value ("star")
bool    -- a data type with two values (tt, ff)
nat     -- a data type with an infinity of values
list α  -- a "polymorphic" type of lists of α values
-/



/- 
**********
EMPTY TYPE
**********
-/

inductive empty : Type

-- Introduction rules

/-
That we defie no constructors for this type
means that is has no introduction rules means
that there are no values of this data type.
It is empty, or uninhabited.
-/

-- Elimination rules

/-
Given any inductively defined data type, we
are given a new elimination axiom, called a
"recursor." In Lean, if the name of a type
is "empty" (for example), its recursor is 
called "empty.rec". Let's see and analyze
what the recursor for the empty type looks
like. Remember: In a nutshell, it's a rule
for (1) constructing a proof of a universal 
generalization, that all values of a given
type have some property, or (2) defining a
function that returns a value for *every*
value of its argument type. 
-/
#check @empty.rec
#check @empty.rec_on

/-
Read Π as meaning the same thing as ∀, and 
(Sort u_1) as meaning either Prop (Sort 0),
in which case we're talking about obtaining
proofs, or Type (Sort 1), in which case we're
talking about obtaining values of functions
that return data values as results.
-/

/-
empty.rec : 
  Π (motive : empty → Sort u_1)     (1)
    (n : empty),                    (2)
  motive n                          (3)

-- same in this case
empty.rec_on : 
  Π (motive : empty → Sort u_1) 
    (n : empty), 
  motive n
-/

/-
Let's consider two variants. First, suppose
u_1 is 0. Sort 0 is the same as Prop, so we're
talking about proving that, given any property 
of values of this type (Lean calls it "motive"),
that any value, n, of this type has this property.
-/

-- Show every value of this type is Blue
-- Suppose values of this type can be Blue
axiom Blue : empty → Prop
-- A "proof by induction" 
theorem all_empty_Blue : ∀ (n : empty), Blue n :=
begin
  assume n,
  apply empty.rec_on, -- no cases to consider
end


/-
Let's define a function that, when given any
value of this type, returns a natural number.
-/

def empty_to_nat : empty → nat :=
begin
  apply empty.rec_on,    -- no cases to consider!
end


/- 
*********
UNIT TYPE
*********
-/

inductive unit : Type
-- one case
| star : unit

-- Introduction

-- star is the one introduction rule, the one value

-- Elimination 

#check @unit.rec      -- first argument is property
#check @unit.rec_on   -- value analyzed is first arg

/-
unit.rec : 
  Π {motive : unit → Sort u_1},   (1)
  motive unit.star →              (2)
  Π (n : unit), motive n          (3)

For any property of unit values (u_1 = 0) 
or any function from unit to another type
(u_1 = 1), if we have a proof or value for 
unit.star, then we have a proof or value 
for every value, n, of this type.

unit.rec_on : 
  Π {motive : unit → Sort u_1} 
    (n : unit), 
    motive unit.star → 
  motive n
-/

/-
A "proof by induction"
-/
theorem all_unit_self_eq : ∀ (u : unit), u = u :=
begin
  assume u,
  apply unit.rec_on u,    -- one case to consider
  apply rfl,              -- proof for that one case
end

/-
A function definition, for a function that for
any values of type unit returns 0, defined "by
recursion."
-/

def unit_to_nat : unit → nat :=
begin
  assume u,
  apply unit.rec_on u,    -- one case to consider
  exact 0,                -- in this case return 0
end

#eval unit_to_nat unit.star


/- BOOL
-/

inductive bool : Type
-- two cases
| ff : bool   -- other case, no arguments
| tt : bool   -- one case, no arguments

-- Two introduction rules, tt and ff


-- Now for the induction principle / elimination rule

#check @bool.rec

/-
A function, Boolean not (!), defined by recursion
-/

def bnot : bool → bool :=
begin
  assume b,
  apply bool.rec_on b,
  /-
  It's a bit of a drag, but you have to keep
  track of which case corresponds to which of
  the constructors, in order.
  -/
  -- case #1: b = bool.ff
  exact bool.tt,
  -- case #2: b = bool.tt
  exact bool.ff,
end

#reduce bnot bool.tt
#reduce bnot bool.ff

/-
How about Boolean or, a binary operation?
-/

def bor : bool → bool → bool :=
begin
  assume b,
  apply bool.rec,
  exact b,
  exact bool.tt,
end

#reduce bor bool.tt bool.tt
#reduce bor bool.tt bool.ff
#reduce bor bool.ff bool.tt
#reduce bor bool.ff bool.ff


/-
A proof using induction
-/
theorem ff_is_id_for_or : 
    ∀ (b : bool), bor b bool.ff = b :=
begin
  assume b,
  apply bool.rec_on b,
  -- case b = bool.ff
  apply rfl,
  -- case b = bool.tt
  apply rfl,
end

/-
In all of the examples we've seen so far,
proof by recursion looks an awful lot like
proof by case analysis. Indeed, we could 
have used cases in all of these examples.
But we'll see in our next examples that in
general there's a fundamental difference:
a proof by induction generally gives you
one or more "induction hypotheses" to work
with, and that can be crucial.
-/

example : 
    ∀ (b : bool), bor b bool.ff = b :=
begin
  assume b,
  cases b,
  -- case b = bool.ff
  apply rfl,
  -- case b = bool.tt
  apply rfl,
end


/- 
***
NAT
***
-/

inductive nat : Type
-- two cases
  | zero              -- base: no arguments       
  | succ (n' : nat)   -- inductive case
/-
Notice that the second constructor givesn 
us a way to construct the next larger natural
number, succ n', from a given smaller natural
number, n'. Now we have a genuinely inductive
definition.
-/


/-
And now we will see where induction differs
from mere case analysis.
-/
#check @nat.rec
#check @nat.rec_on

/-
nat.rec :
  Π {motive : nat → Sort u_1},
    motive nat.zero → 
    (Π (n' : nat), motive n' → motive n'.succ) → 
    Π (n : nat), motive n

Given any propery or function on natural numbers
(motive), if you're given a proof/answer for zero,
and if for any natural number if you have a way to
derive proof/answer for n'+1 from a proof/answer 
for n', then you can construct a proof/answer for
any natural number, n.

nat.rec_on :
Π {motive : nat → Sort u_1},                      (1)
    motive nat.zero →                             (2)
    (Π (n' : nat), motive n' → motive n'.succ) →  (3)
    Π (n : nat), motive n                         (4)

Sort u_1 could be Prop (Sort 0), or Type (Sort 1), or other.

Given that here's how we can read this axiom.

(1) given any property of natural numbers, or any
function from natural numbers to values of another
type, ...
(2) if the property holds, or we have an answer, for
the case of nat.zero, then ...

(3) if whenever we have an answer, or the property holds,
for an arbitrary natural number n', we can derive a proof
or answer for the successor of n' (nat.succ n' or n'.succ
or simply n' + 1)

(4) then the property holds, or we have an answer, for
*all* values of type nat.

Suppose you need a proof for n = 3, for example. If
you have an answer for 0, start with that, then you
can apply the method for producing a proof/answer for
the next larger number to 0 to get a proof/answer for
1, then apply it again, etc., until you have the proof
or answer you need for n = 3, or for any n whatsoever.
-/

/-
For the remaining examples involving natural numbers, 
we'll close the namespace in which we've defined our
own local version of nat (same as Lean's) so that we
can take advantage of Lean's definitions of functions
applicable to natural numbers, such as addition.
-/
end hidden

-- Sum up natural numbers from 0 up to argument (n) 
def sum_to : nat → nat :=
begin
assume n,
-- construct function by induction/recursion
-- have to give partial answers for two cases
apply nat.rec_on n,
-- answer for base case, n = 0
exact 0,
-- show if we have answer for n' we can derive answer one for n'+1
assume n',              -- suppose n' is arbitrary
assume result_for_n',   -- assume result for n' (ind. hypothesis)
exact result_for_n' + (n' + 1),   -- answer for n' + 1
end


#reduce sum_to 0
#reduce sum_to 1
#reduce sum_to 2
#reduce sum_to 3
#reduce sum_to 4
#reduce sum_to 5

/-
EXERCISE: Define the factorial function by recursion
-/

def factorial : nat → nat :=
begin
end

/-
Lean provides a nice notation for writing proofs
or functions by induction/recursion. Let's rewrite
our sum_up function using it. First you get the 
function name (sum_up_to) and type (nat → nat).
The the set of argument values is partitioned by
the matching rules, one per line, with a pattern,
then := then the answer for arguments that match.
-/

def sum_up_to : nat → nat 
| (nat.zero)    := nat.zero
| (nat.succ n') := sum_up_to n' + (n' + 1)

/-
The first rule gives you an answer for the base
case, the second *assumes* you have an answer for
n' and constructs an answer for n' + 1. Another way
to think about it is that it gives you a way to 
turn an answer or result for any n' into an answer
or result for n'+1. 

Now with an answer for the base case and a 
rule for induction, you have the components
to define a function converts *any* argument 
value into the desired result value. You get
a proof of a universal generalization. You
get a function that you can apply to *data*
values to get *data* results.  

As an example, consider the input, n = 5. This
value can be expressed as (nat.succ 4) and that
is how to understand the second case. It matches
the argument based on how it was constructed, in
this case by the succ constructor, not by zero, 
and pulls out the argument, n'=4, to which succ
was applied (to get 5 as the argument value). 
In this case, the right answer is the sum of 
(1) the answer to the question what is the 
sum of all numbers from zero up to n'=4, and
(2) (n'+1)=5. The "answer for 4" is 10, plus 
5 as the argument value is 15.

LESSON: A recursive function is defined in terms of
(1) assumed solutions to smaller sub-problems, and (2)
a combining of these solutions with an argument value
to produce answer for that argument value. 
-/

#reduce sum_up_to 5




/-
LECTURE 29
-/

/-
To review, last time we ended by using
induction to define a function that sums
up the numbers from 0 to any natural number
given as an argument. 
-/

#reduce sum_up_to 5

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
  apply nat.rec_on n,

  -- in case we're given the argument, zero, return m
  exact m,

  -- else from n' and answer for n' derive answer for n'+1
  assume n',                    -- n'
  assume answer_for_n',         -- answer for n'
  /-
  Show that from n' and an answer for n' you can
  produce an answer for n' + 1. As long as you also
  have an answer for a base case, such as zero, you
  can derive answers for that or any greater argument.
  -/
  exact nat.succ answer_for_n', -- the right answer for n'+1
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
Proofs
-/

/-
In the definition of my_add' we can see 
readily that we have an "answer" for each
of two cases for n, the argument to the
function.

(1) n = nat.zero (first constructor)
(2) n = nat.succ n' for some n' (second constructor)

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

example : ∀ (m : ℕ), my_add' m 0 = m :=
begin
    assume m,
    /-
    Proof by induction. 
    -/
    apply nat.rec_on m,

    -- base case, m = 0
    exact rfl,

    -- inductive case
    assume n',        -- n'
    assume ih,        -- answer/result for n'

    -- simplify goal using rules defined in my_add'
    simp [my_add'],

    -- our assumption now finishes the proof
    assumption,
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


/- LISTS
-/

namespace hidden 
inductive list (α : Type) : Type 
| nil : list
| cons (h : α) (t : list) : list


end hidden

