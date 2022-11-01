
/--
Increasing the arity
--/

/-
Now it generalizes again. A predicate with two arguments
define a set of ordered pairs: all those pairs that satisfy
whatever condition is specified.

Here's for example, is a specification of all pairs, (n m), 
of natural numbers, where the second element, m, of a pair,
is equal to the square of the first element, n, where square
in turn is defined as so:
-/

def square (n : ℕ) := n * n

/-
Now we specific the relevant set of pairs.
-/
def squares (n m : ℕ) : Prop := square n = m 

/-
We can prove pairs that bear this relationship and
not ones that don't.
-/

example : squares 0 0 := rfl
example : squares 0 0 := rfl
example : squares 1 1 := rfl
example : squares 2 3 := rfl    -- no can, dude
example : squares 2 4 := rfl
example : squares 25 625 := rfl


def squares2 := 
