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
  Π (motive : empty → Sort u_1)     (1) property
    (n : empty),                    (2) arbitrary value
  motive n                          (3) proof value has property

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
Lean provide induction tactic to apply the right
induction axiom and clean up automatically. 
-/
def empty_to_nat : empty → nat :=
begin
  assume e,
  induction e,    -- no cases to consider!
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
  Π {motive : unit → Sort u_1},   (1) property
  motive unit.star →              (2) proof for star
  Π (n : unit), motive n          (3) proof for all

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
The induction tactic in Lean applies the right
induction principle given the type of the target
and gives you additional helpful information, such
as good names for the cases it considers.
-/
example : ∀ (u : unit), u = u :=
begin
  assume u,
  induction u,    -- one case to consider
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

-- using the induction tactic

example : unit → nat :=
begin
  assume u,
  induction u,    -- one case to consider
  exact 0,                -- in this case return 0
end

-- We can apply these functions and they compute!
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
bool.rec : 
  Π {
    motive : bool → Sort u_1},      -- property
    motive bool.ff →                -- proof for tt
    motive bool.tt →                -- proof for ff
    Π (n : bool), motive n          -- proof for all bool

To prove that *all* values of type bool
have some property or a corresponding value,
it suffices to prove proofs/values for tt and
for ff.
-/

/-
A function, Boolean not (!), defined by recursion
-/

def bnot : bool → bool :=
begin
  assume b,
  apply bool.rec_on b,
  /-
  Reduce problem of giving an answer for all
  Boolean arguments to the two subproblems of
  providing an answer for tt and an answer for ff. 

  It's a bit of a drag, but in Lean when you 
  rec or rec_on directly, you have to keep track
  of which case corresponds to which constructor, 
  in the order they're listed in the data type
  definition.
  -/
  -- case #1: b = bool.ff
  exact bool.tt,
  -- case #2: b = bool.tt
  exact bool.ff,
end

-- it's better to use the induction tactic
def bnot : bool → bool :=
begin
  assume b,
  induction b,  -- the cases are now well marked
  -- case #1: return value when b = bool.ff
  exact bool.tt,
  -- case #2: return value when b = bool.tt
  exact bool.ff,
end

#reduce bnot bool.tt
#reduce bnot bool.ff

/-
We can define *binary* functions this way too. 
Here's our own version of Boolean or.
-/

def bor : bool → bool → bool :=
begin
  assume b1 b2,
  apply bool.rec_on b1,
  -- first argument is false (ff)
  exact b2,
  -- first argument is true (tt)
  exact bool.tt,
end

-- now using induction tactic
def bor' : bool → bool → bool :=
begin
  assume b1 b2,
  induction b1,
  exact b2,
  exact bool.tt,
end

#reduce bor' bool.tt bool.tt
#reduce bor' bool.tt bool.ff
#reduce bor' bool.ff bool.tt
#reduce bor' bool.ff bool.ff


/-
Now let's prove a proposition about
Boolean values, namely that for any
b, b ∨ ff = b. In mathematical terms,
we want to prove that ff is a "right
identity element" for the Boolean or
operation.
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

-- Using induction tactic
theorem ff_is_id_for_or' : 
    ∀ (b : bool), bor b bool.ff = b :=
begin
  assume b,
  induction b,
  repeat { apply rfl },
end

/-
PROOF BY INDUCTION vs PROOF BY CASES
-/

/-
In all of the examples we've seen so far,
proof by induction looks an awful lot like
proof by case analysis. Indeed, we could 
have used cases in all of these examples.
Here's a construction for the preceding
example using a proof by cases "strategy."
-/

-- Proof by cases: ff is a right identity for "or"
example : 
    ∀ (b : bool), bor b bool.ff = b :=
begin
  assume b,
  cases b,
  apply rfl,
  apply rfl,
end

/-
But now we'll see where these strategies differ.
The difference shows up when larger values of a
given type can beconstructed from smaller values
of the same type.
-/


/- 
***
NAT
***
-/


/-
We're now going to meet the inductve data
type definition for the type in Lean called
nat (ℕ). It's the type the terms/values of
which representing natural numbers, from 0
on up ad infinitum. 
 
For data types that are genuinely inductive
in this sense, and not just enumerations of
constant terms (as in the cases above, e.g.,
bool, where we have just two constant terms,
tt and ff), there is a big difference between 
proof by cases and by applying an induction
axiom. With induction, you have additional
assumptions ("induction hypotheses") to work 
with, as we'll now explain. 
-/

/-
We'll look in particular at the induction
principle for natural numbers. As with any
type, a proof constructed by applying its
induction axiom is a "proof by induction." 
When the type is nat, such a proof is often
called a proof by "mathematical" induction.

So let us first look at the definition of the
nat type, then we'll see how its induction
principle can be used to produce both:
- logical proofs of logical propositions 
- computational return values of functions 
*for any* natural number, n.
-/

inductive nat : Type
-- two cases
  | zero              -- base: no arguments       
  | succ (n' : nat)   -- inductive case
/-
The induction principle will follow from the
structure of the data definition. For each of
the ways of building a value of this type, we
will require rule/machine/answer/proof for all
values that can be produced in that manner. So
let's first be sure we see how this data type
definition defines an infinite set of terms
that we can consider to represent natural
numbers. (There's a one-to-one corresondence).
-/

def two : nat := 
  nat.succ (
  nat.succ 
  nat.zero)

/-
Now let's talk about proovin universal generalizations
over natural numbers -- by induction!

Suppose P : nat → Prop specifies a property of 
natural numbers. Then induction takes P as well
as proofs of two smaller "lemmas" and produces
a proof of ∀ n, P n: that every natural number
has property P. 

Suppose P : nat → β specifies a function, from  
natural numbers to some *data type* (like nat
or string, but not Prop). Then induction takes 
P and two "smaller" functions, which we will
talk about more momentarily, and uses them to
return function that returns the right result
when the function is applied to *any* natural
number n. The Lean type of the final result is 
Π (n : nat), nat. The Π (capital pi) means 
"for any." ∀ is another notation for Π, so the
result is of type, ∀ (n : nat), nat, and that
is the real meaning of the type, nat → nat. 

You know have the vocabulary to understand and
answer the following question about "functions"
in Lean" What special properties of functions do
they all have? 
-/


/-
So what are the two smaller "machines" that you
have to provide to the induction principle to get
a general theorem or function?

Let's revisit our story about two machines
that can build a building of any height.
The first can lay down a ground floor, and
that's all it's good for. The second one
has to be given a floor, let's say floor 
n', to start with, and it then builds the
next floor up, number n'+1.

Neither machine is of much use itself. The
first only lays down the ground floor (#0).
The second has to have a floor to start on
or it can't run to do its job.

Together, though, these machines can build 
a building of any height. Suppose you want
a building with floors numbered 0 ... n. 
Start by running the first machine once to
build floor 0; then run the second machine
n times, each time giving the floor output
by the last run as an input to the next.
That gives you the building height you want.

A proof by induction of a proposition that
claims that some property holds for every
natural number requires that you provide 
two analogous machines, but instead of 
imaginary buildings they generate proofs,
that for any n, n has the stated property.

As we've said, this principle can also be 
used to construction total functions from
natural numbers to results of any other data
type.

The first machine generate a proof for the case
where n = 0. The second machine then takes number,
n' and a proof that n' has that property (a floor 
to start on) and constructs and returns a proof 
that n'+1 has the property!

NOTE WELL: The second machine takes two arguments,
any natural number, n', and a proof/answer for n',
and it uses these two arguments (also often called
induction hypotheses) to construct a proof for the
next larger n', n'+1, aka n'.succ or (succ n').

The machines in our case correspond to the
constructors defined by the data type. The 
nat data type has two natural-number-building
constructor machines. The first (zero : nat), 
defines "the ground floor" in the stack of
natural numbers: it's just constant zero. 

In a proof by induction of the proposition
that every natural number has some property,
P, the first machine emits a proof of (P 0),
that 0 has the property specified by P.

The second nat constructor, by contrast, is
a function, (succ : nat → nat). When appled
to a given nat, n' (a floor to start on), it
emits (succ n'), representing n'+1, the 
"next floor up." 
  
In proof by induction of (∀ n, P n), every
natural number has property P, the second
machine takes any number n' and a proof of
(P n') and must convert these into a proof
of (P (succ n')), that is, of P (n' + 1). 

If you have both such machines, then you can
build a proof for any given natural number, 
n, whatsoever, and from this fact deduce that
every natural number has that property. QED.

In general, therefore, to give a proof by
mathematical induction requires that you
provide two machines: one that gives you a
proof for 0, and one that takes any n' and
a proof/answer, P n', for n', and returns 
a proof/answer for P (n' + 1). 

The induction principle for the nat type
thus says that in order to prove ∀ n, P n,
it suffices to have two "machines": a proof
of P 0, and a *function* that when given 
an arbitrary n' and proof/result (P n') 
then returns a proof/result(P (n'+1)).
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
induction n with n' ih,
-- answer for base case, n = 0
exact 0,
-- show if we have answer for n' we can derive answer one for n'+1
--assume n',              -- suppose n' is arbitrary
--assume result_for_n',   -- assume result for n' (ind. hypothesis)
exact ih + (n'+1),  -- answer for n' + 1
end

#eval sum_to 100

#check @nat.rec_on
/-
Π 
  {motive : ℕ → Sort u_1} 
  (n : ℕ), 
  motive 0 → 
  (Π (n : ℕ), motive n → motive n.succ) → 
  motive n
-/


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
  assume n,
  induction n with n' n'_ih,
  -- with names for arguments to second machine
  -- first machine, answers for zero
  exact nat.zero.succ,
  -- second: given n', answer n', answers for n'+1
  exact n'_ih * (n'.succ)
end

#eval factorial 10


/-
Now that you understand how the inducion 
principle for a type enables you to define
total functions on values of that type, we
introduce a more convenient notation. Here
is the same function defined basically in
the same way, with two rules, one for each
form of input considered: zero or succ n'.
Each rule starts with |, presents a pattern
for "matching" input values (including the
binding of names to parts of these values),
has a := and then constructs an answer for
any such value (often involving values that
are given names during pattern matching). 
-/
def fac : ℕ → ℕ 
/-
If the argument to this function matches
"nat.zero", emit the answer, 1, the value 
of 0!
-/
| (nat.zero) := 1
/-
If the argument in (n'+1) and we have the
answer for n', i.e., the value of fac n',
i.e., the product of all of the numbers 
from 1 to n', then the answer for n'+1 is  
fac n' * (n"+1), the product of all of the
numbers from 1 to n'+1.  
-/
| (nat.succ n') := fac n' * (nat.succ n') 

-- It works! The result is a total function
#eval fac 10
#eval fac 20
#eval fac 30
#eval fac 40
#eval fac 50

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

LESSON: The induction principle for type reduces 
the problem of a defining a total function on 
values of that type to two smaller problems: one
is to produce an answer for the argument value, 0.
The second is to define a machine (function) that
when given any number n' and an answer for n'
uses that information to construct an answer for
(n'+1). 
-/