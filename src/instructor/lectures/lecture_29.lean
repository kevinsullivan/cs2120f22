import algebra.algebra.basic tactic.ring

/-
In this lecture we pull together all of the 
elements of a completely formal and checked 
proof by induction of the claim that the sum
of the natural numbrtd from 0 to n is equal 
to n(n*1)/2. 

This specific theorem is interesting. The
larger  is that the end-to-end example we
give you here can serve as model for how to
prove a generalization, (∀ n, P n), using
the induction axiom for the type of n. All
of the essential elements of any such proof 
are highlighted here and the completeness
and correctness of this example is formally
proved.
-/


namespace hidden

-- Data type

/-
As we've discussed, every inductively
defined data type comes with it own
induction rule, a rule for proving a
universal generalization of values of
that type. 

To be more precise, if α is a type and 
P : α → Prop is a predicate on (property 
of) values of this type, the induction
can be applied to prove ∀ (a : α), P a.
The induction rule takes P implicitly 
along with proofs of specified lemmas,
yielding a proof of ∀ a, P a in return.

Recall the specific example where α is
bool. If P is a property, we can prove
it holds for all values of type bool
by having proofs that it holds for each
of its two values, tt and ff in Lean.
-/

/-
Things are much more interesting when
we apply induction to prove universal
generalizations about natural numbers,
∀ n, P n. 
-/

inductive nat : Type 
| zero : nat 
| succ  (n' : nat) : nat

/-
Data introduction rules are generally
called constructors. The first here takes 
no arguments and thus defines a constant 
term of this type. The second constructor
applied to a term of type nat constitutes
a new term also of type nat. It gives us
a way to incorporating a given nat term,
n', into a new term, (succ n'), which we
take as representing one more than n'.

Focus on that idea: a term of type nat
is either zero or its a term, (succ n'),
that includes a sub-term, n', also of
type nat. If a term of type nat isn't
zero, it's thus one of these "nested"
structures, namely "succ" applied to a
smaller term, n', also of type nat.
-/

-- Examples and tests

/--/
For now, let's practice with, demonstrate,
and test our new definition by giving some
examples of, and bindings names to terms 
of this type, nat.
-/
def zero := nat.zero
def one := nat.succ zero
def two := nat.succ one
def four := nat.succ
            (nat.succ
            (nat.succ
            (nat.succ
             nat.zero)))

/-
Problem #1: Fill in the blank with a term
of type nat that we've agreed interpret as
representing the natural number, 3. Use the
"expanded style" used to define four above
to give your answer here. 
-/
def three : nat := _


#check zero
#reduce zero
#check four
#reduce four

/-
Now having define a data type to represent
natural numbers, we'll need some operatons 
on values of this type.
-/

-- Operations

/-
We'll start with a simplest of unary
operations. We'll call it inc, short
for increment. Given any value, n, of
type nat, it reduces to (returns) succ 
n. We first give this function as an
example using our scripting notation,
and then, with the name, "inc", using
Lean's notation for defiing functions
by cases.  
-/

-- increment function
-- scripting notation
example : nat → nat :=
begin
  assume n,
  exact (nat.succ n)
end

-- increment function 
-- cases notation
example : nat → nat
| n := (nat.succ n)

-- increment function 
-- lambda notation
example : nat → nat := 
  λ n, (nat.succ n)

-- increment function, named inc
def inc := λ n, (nat.succ n)

-- Testing / demonstration

#reduce inc zero
#reduce inc four


-- Data elimination by pattern matching

/-
The next operation (function) we define
is the decrement function: the function
that takes any natural number, n, and 
that returns 0 if n equals 0, and n' if 
n equals nat.succ n'. As you can see, 
there are two cases that we naturally
have to consider here, with different
behaviors in the different cases, and
the different cases corresponding to 
which constructor was used to produce
the value, n, assumed to be given as 
an argument. We are drive to define
our function *by cases*, one for each
of two possible forms of argument: 
either nat.zero or nat.succ n', where
n' is itself a (one smaller) term of
this same type, nat. 

Given a non-zero nat, the decrement 
function basically removes a single 
"succ" constructor application to
reveal the one-smaller nat value to
which it must have been applied, and
then "returns" that one-smaller number.  

To do this requires that we be able
to "analyze" a given term to see how
it was assembled (which constructor)
and from what parts (what arguments).
This analysis process is usually called
"pattern matching". Given a value, n, 
of type nat, pattern matching will let 
us determine which constructor was
used to construct the argument value
and to what arguments it was applied.

As an example, the pattern (nat.succ n')
cannot match the term nat.zero, as the
constructors themselves differ. It can,
however, match (four : nat) as defined
above, and in doing so it will bind the
name, n', to the argument to which the
succ constructor must have been applied
to produce the value, four. n' is thus
bound to nat.zero.succ.succ.succ (that
is, 3). In effect, we reach into the
representation of "four" to grab the 
"three" from which it was built, and
we return that. 

A set of pattern matching rules of this
kind will define a function by cases, 
with a separate reduction rule (right
hand side) for each pattern matching
case. Such a set of rules proves a way
to *use* a value of a given type and
so constitutes a kind of elimination
rule for an arbitrary data value of a
given type -- by cases.
-/

def dec : nat → nat 
| (nat.zero) := nat.zero
| (nat.succ n') := n'

-- addition

/-
While we won't ue the dec function
in expressing or proving our main
conjecture, we will use the concept
of pattern match to define addition
as an operation that we will need
(just to express the notion of the
sum of a sequence of numbers).

Our definition of addition is by
case analysis on the first argument 
to add. Consider the expression, 
(add one two), for example. The 
idea is that to add the first value
to the second, we want to apply 
the succ function to the second
as many ties as specified by the
first argument. An the way this 
is done is by induction: on the
right hand side of the rule for
nat.succ n' we can *assume* we
know both n' *and* (add n' m).

If it's zero,
we return the second argument
-/

def add : nat → nat → nat 
| (nat.zero) (m) := m
| (nat.succ n') (m) := nat.succ (add n' m)

def mul : nat → nat → nat
| (nat.zero) (m) := nat.zero
| (nat.succ n') (m) := add (m) (mul n' m)

/-
Homework: Define exp n m to compute the value
of n raised to the m'th power.
-/

/-
Finally, here is a formal specification of 
our sum_to function. The key idea is that 
if you know the sum of all the numbers from
0 to n', you can easily compute the sum of
all the numbers from 0 to n' + 1 by simply
adding n' + 1 to the given result for n'.
Seeing how to produce proofs of the "step"
lemma(s) is the challenge and key to proofs
by induction. 

Remember: you can assume that you're given
n' and the answer for n'. The latter is
available by a recursive call with n' as
an argument. From these two values you have
to construct an answer for n'+1. That's it.
-/
def sum_to : nat → nat 
| (nat.zero) := nat.zero
| (nat.succ n') := add (sum_to n') (n'.succ) 

/-
Conclusion: We now have all the key elements first
to express our proposition and then to prove it by
induction. Continue to the next file.
-/

-- Tests and demonstrations
#reduce sum_to four
#reduce mul four four
#reduce add four three
#reduce inc four

end hidden

