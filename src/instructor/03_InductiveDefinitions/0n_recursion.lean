

/-
You should (almost must) use this "by cases" syntax
to define functions recursive functions. If you use
other syntax, you'll find that you won't be able to
have the function body call the function itself.
-/

def factorial' (n : ℕ) : ℕ :=
  if n = 0 
  then 1 
  else n * factorial' (n-1)      -- factorial not defined


def factorial : ℕ → ℕ           -- remember, no := here
| 0 := 1
| (n' + 1) := (n' + 1) * factorial n'


-- Lean can't prove termination recursive call is passed f(n) for some function, n
def factorial2 : ℕ → ℕ           -- remember, no := here
| 0 := 1
| n := n * factorial2 (n-1)     -- can't prove termination

/-
The problem with the preceding code, for reasons we
can't really get into very deeply right now, is that
Lean can't tell that the argument to factorial2 will
decrease in value on each recursive call, because all
it sees is a function (subtraction) applied to n, and
it doesn't try to analyze the result. On the other
hand, if n = (n' + 1), Lean knows that n' is one
smaller than n, so if n is the argument into the
function and it calls itself recursively to n', it
Lean will "see" that the argument passed to the
recursive call is always less than n, and so it can
guarantee the recursion terminates (with the base
case). 
-/

#eval factorial 5



