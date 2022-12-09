-- UNDER CONSTRUCTION. IGNORE.


/-
Now that we've defined our base and step
"machines" (lemmas), we assemble them into
an overall proof by applying the induction
axiom to them.
-/
theorem left_zero : ∀ n, 0 + n = n := _

/-
EXERCISE: Reformulate the formal proof in
the class notes, ∀ n, 0 + n = n := _ to
use Lean's induction tactic.
-/


/-
EXERCISE: Give a fluent English-language proof
(based on the formal proof).

EXERCISE: Give a fluent English-language proof
that 2 * sum_to n = n * (n+1). Show all of the
algebraic steps needed to complete this proof.
If you need to transform expressions using the
associativity or commutativity of addition or
multiplication, say so. Each step must have a
justification.

EXERCISE: Give an English language proof by
induction of the proposition that, for any
natural number, n, a set with n elements has
2^n subsets. 

EXERCISE: Prove by induction that ∀ n, P n, 
where P n is the proposition that the sum of 
all the squares of the natural numbers from 
0 to n = (n(n+1)(2n+1))/6.

A. Using the induction axiom for the natural
numbers, applied to base and step functions
that you define separately, to implement a
function that computes this sum of squares 
for any natural number, n.  Write a few test
cases to check that your function appears to
be working, at least for n = 0, 1, 3, and 5.

B. Formally express the property of a natural
number, P n, that asserts that the sum of the
squares of the numbers from 0 to any given n
equals (n(n+1)(2n+1))/6.

C. Define the proposition that every natural
number, n, has this property. This is what is
to be proved by induction.

D. Define a proof of the base case, n = 0.

E. Define a proof for the inductive or step
case, amounting to a function that, when given 
any n' and a proof of P n' returns a proof of
P (n' + 1).

F. Construct a proof of the proposition that
every natural number has this property by
applying the induction axiom for the natural
numbers to n and the base and step proofs.

G. Give a fluent English-language proof of
the universal generalization based on the
work done above. Show *all* of your algebra
work.
-/

