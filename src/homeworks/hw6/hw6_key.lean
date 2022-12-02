import data.set

universes u v   -- Universe levels, don't worry

/-
Homework #6: Functions, Sets, Relations
-/


/- #1. Basic Functions [35 points]-/


/- A [5 points].

Write a function, isZero, using "by cases" syntax, 
that takes any natural number, n, as an argument and 
returns a Boolean result, true if n = 0 and false if
n > 0 (i.e., n = n' + 1 = (nat.succ n') for some n').
(Don't get distracted by unnecessary details.)
-/

def isZero : ℕ → bool
| 0 := tt
| _ := ff


-- These test cases should pass except the last 
example : isZero 0 = tt := rfl
example : isZero 1 = ff := rfl
example : isZero 2 = ff := rfl
example : isZero 3 = tt := rfl    -- tester tester



/- B [10 points].

Here's a function, fib, using "by cases" syntax, that
takes any natural number, n, as an argument and that
returns the n'th Fibonacci number. The n'th Fibonacci
number is defined by cases: when n is 0, it's 0; when
n is 1 (nat.succ nat.zero), it's 1, otherwise, in the
case where n = n' + 2, it's fib n' + fib n'+1
-/

def fib : ℕ → ℕ 
| 0 := 0
| 1 := 1
| (n' + 2) := fib n' + fib (n' + 1)

-- These test cases should pass except the last 
example : fib 0 = 0 := rfl
example : fib 1 = 1 := rfl 
example : fib 2 = 1 := rfl
example : fib 3 = 2 := rfl
example : fib 4 = 3 := rfl
example : fib 5 = 5 := rfl
example : fib 10 = 55 := rfl
example : fib 2 = 2 := rfl    -- tester tester



/- C [10 points]
Write a function, add, that takes two natural 
numbers and computes their sum. You may *not*
use the addition function that Lean defines in
its libraries. Your addition function should 
be defined by cases. Given arguments n and m,
if m is zero, just return n; otherwise, if m
is (m' + 1), return the sum of n and m' plus
one. (That's still the right answer, right!)
-/

def add : ℕ → ℕ → ℕ 
| n 0 := n
| n (m' + 1) := (add n m') + 1

-- These test cases should pass except the last 
example : add 0 0 = 0 := rfl
example : add 5 0 = 5 := rfl
example : add 0 5 = 5 := rfl
example : add 1 1 = 2 := rfl
example : add 1 2 = 3 := rfl
example : add 2 2 = 4 := rfl
example : add 3 2 = 4 := rfl  -- tester tester


/- D [10 points]

A function is said to be involutive, or an
involution, if applying it twice to *any* value
(of the right type) returns that original value. 
For example, if f is a function, and a is any
argument, then f is involutive if f (f a) = a.
Formally define involutive as a property of
any function, f : α → α. 
-/

def involutive {α : Sort u} (f : α → α) := 
  ∀ (a : α), f (f a) = a 

/-
Now prove the proposition that the Boolean negation 
function, called bnot in Lean, is an involution. The
trick here is simply to pick the right proof strategy.
Ask, how can I prove it? Hint: It's just a bool!
-/

example : involutive bnot :=
begin
-- By the definition of involutive ...
unfold involutive,

-- ... we are to
show  ∀ (b : bool), !!b = b, 

-- To start we assume b to be an arbitrary bool value.
assume b,

-- We then show that in all cases (b=tt, b=ff) that !!b = b
cases b,

-- In all cases the conclusion is true.
exact rfl,
exact rfl,

-- QED
end 


/- 2 Sets [35 points] -/


/- A [5 points].

Formally define a predicate, perfectSquare,
satisfied by any natural number that is the 
square of some other natural number. 25 is a
perfect square, for example, because it's the
square of the natural number 5. Fill in both
underscores in the following skeleton to give
your answer. Remember: Predicates take values
to propositions. 
-/

def perfectSquare (n : ℕ) : Prop := ∃ m, m*m = n


/- B [5 points].

Define the set of all perfect squares using
set comprehension (set builder) notation and
the perfectSquare predicate.
-/

def perfectSquares : set ℕ := { n | perfectSquare n }


/- C [5 point].

State and prove the proposition that 25 is in
the set of perfect squares. Use set membership
notation in writing your proposition.
-/


example : 25 ∈ perfectSquares :=
begin
-- Expanding the definition of perfectSquares, ...
unfold perfectSquares,

-- We are to ...
show perfectSquare 25,

-- Expanding the definition of perfectSquare, ...
unfold perfectSquare,

-- We are to show that 
show ∃ (m : ℕ), m * m = 25,

-- The challenge in proving a ∃ is to find/compute a witness
-- Here it's easy to see that the witness has to be 5
apply exists.intro 5,

-- The rest is by simple algebra and reflexivity of equality
trivial,
end


/- D [20 points].
Consider the following sets of natural numbers:

X = { 2, 3, 4}
Y = { 4, 5, 6}
-/

def X : set ℕ := { 2, 3, 4 }
def Y : set ℕ := { 4, 5, 6 }

/-
Formally state and prove the following propositions
using set and set operator notations.

1. 4 is "in" the intersection of X and Y
2. 4 is in the union of X and Y
3. 4 is not in the set difference, X \ Y
4. 10 is in the complement of X
-/


-- 1
example : 4 ∈ X :=
begin
-- It's easier if we expand the definition of X
unfold X,

-- What we now need to show is
show 4 = 2 ∨ 4 = 3 ∨ 4 = 4,

-- Remembering ∨ is right associative, we can prove the right side
right,

-- And again
right,

-- And the rest is trivial
exact rfl,

-- QED
end

-- 2
example : 4 ∈ (X ∪ Y) :=
begin
-- Unfolding the definitions of X and Y ...
unfold X Y,

-- we are to show 
show (4 = 2 ∨ 4 = 3 ∨ 4 = 4) ∨ (4 = 4 ∨ 4 = 5 ∨ 4 = 6),

-- We can prove either side, but the right is easier
right,

-- We can prove the left disjunct
left,
exact rfl,

-- And we're done. QED.
end

/-
Hint: IN the following problem, you 
might want to fact that 4 ∈ {4, 5, 6} 
without stopping to prove it.  Here's a 
nice trick/tactic: 

let n : 4 ∈ {4, 5, 6} := _

This will put the assumption, n, in your
context, but with a note attached saying
that you still need a proof of it. Don't
worry about the crazy goal set after you
use this hint (if you do). Just do what 
you've learned to do looking at the top
goal carefully and choosing the right 
next oroof strategy.
-/

-- 3
example : 4 ∉ (X \ Y) :=
begin
-- Unfolding X and Y we see that ...
unfold X Y,

-- ... we must  
show 4 ∈ {2, 3, 4} \ {4, 5, 6}  → false,

-- The proof of this is by negation. We assume the premise
assume h,

-- and show that that leads to a contradiction

/-
A case analysis on this assumption indicates that
we have to prove 4 is in the left and not in the
right set
-/
cases h with x y,

/-
But 4 is in the right-hand set. So that's going
to produce a contradiction. Let's just assert that
4 is in the right hand set (and we'll prove it later).
-/
let n : 4 ∈ {4, 5, 6} := _, -- _ is the missing proof

-- We now have our contradiction
contradiction,

-- All we need now is that delayed proof ...
left,
exact rfl,

-- That's easy to prove. QED.
end


-- 4. 10 ∈ Xᶜ 

example : 10 ∈ Xᶜ :=
begin
-- We'll start by expanding the definition of X
unfold X,

-- What we must now show is that ¬ (10 ∈ {2, 3, 4}).
-- The prove is by negation.
assume h,

-- But 10 is not in {2, 3, 4}, 
-- as revealed by repeated analysis of h
repeat { cases h },   
end 



/- 3. Relations [30 points] -/

/- A [15 points].

State and prove the proposition that any 
function, f, in Lean, from any type α to any
type β, is single valued. 
-/

/- 1 [5 point].
Formally define single-valuedness for any 
binary relation r : α → β → Prop. If r is 
single valued then r x can have two values, 
say y and z, only if y = z. Think about this
hard enough that it really makes sense to you. 
-/

def single_valued   -- predicate on relations
{α β : Type} 
(r : α → β → Prop) 
: Prop :=  
  ∀ a x y, r a x → r a y → x = y

/- 2 [5 points]

Define a relation sqrs : ℕ → ℕ → Prop where sq x y
means that y is the square of x. 
-/

def sqrs : ℕ → ℕ → Prop 
| x y := y = x * x

/- 3 [5 points] 

Now formally state and prove the proposition
that the sqrs relation is single-valued.
-/

example : single_valued sqrs :=
begin
-- By expanding the definitions of single_valued and sqrs ... 
unfold single_valued sqrs,

-- ... we see that we are to ,,,
show ∀ (a x y : ℕ), x = a * a → y = a * a → x = y,

-- We assume the premises 
assume a x y hx hy,

-- and now need to show that x = y, which is done 
-- by rewriting both x and y to a*a (using eq elimination)
rw hx,
rw hy,

-- A final (Lean-automated) application of reflexivity of
-- equality finishes the proof. QED.
end


/- B [5 points]

A mathematical function, f : α → β, is said 
to be injective if it never relates different 
α (first) values to the same β (second) value. 
The only way an injective function f can relate 
a to x and also b to x, is if a = b. A function
that satisfies this constraint is injective.
-/

def injective 
(α : Sort u)        -- any type from any universe
(β : Sort v)        -- any type from any universe
(r : α → β → Prop)  -- any relation on α and β 
(a b : α)           -- any two arbitrary α values
(x : β) :           -- any β value
Prop := 
  -- Answer
  r a x →           -- if r relates a to x, and
  r b x →           -- if r relates b to x, then 
  a = b             -- injectivity demands a = b


/- C [10 points].

A mathematical function, f : α → β, is said to be 
a total function if it's defined (there is some 
β value) for all α values. ∀ (a : α), β. Indeed,
this is the meaning of the notation α → β in Lean
and similar logics. The upshot is that functions 
in Lean can only be total.  Complete the following
proof that every function in Lean is total.
-/

example : 
  ∀ (α β : Type) 
  (f : α → β), 
    ∀ (a : α), 
      ∃ (b : β), 
        f a = b :=
begin
-- Assume the given conditions
assume α β f a, 

/- 
Given a, and given the fact that "functions" in Lean 
must be total, we can of course compute a b such that 
f a = b, and that done by just computing f a. Totality
of f means that this application must and will return
result of type β. So we can just use that value as a
witness to prove  that ∃ (b : β), f a = b. 
-/
apply exists.intro (f a),

-- The rest is ... 
trivial,

-- QED
end

