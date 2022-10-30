/- FUNCTIONS -/

/- INTRODUCTION

Until this point in this class, we have
worked mostly "in Prop" (with propositions
and proofs). That makes sense because we 
were studying predicate logic.

We still are, but now that we know basic
reasoning principles, we're going to home
in on *functions* as an essential part of
the syntax and semantics of predicate logic. 

Predicate logic supports function symbols 
in expressions and application expressions,
where function symbols are applied to one
or more arguments of the right types. 

The constructive logic of Lean provides the 
means to define functions, apply them, use
their names in propositions, and use them in
constructing proofs. It's valuable and indeed
remarkable to have an environment in which 
you can do correct logical reasoning with
functions that *actually compute*! It moves
the study of logic a studying in computer
science. 

Summary statement: function and applications of
functions to arguments yielding results are part
of the essential core of classical first-order 
and constructive predicate logic. In constructive
logic we can not only define functions in precise
and pure mathematical terms, but these functions
will run. By choosing the better logic in which 
to learn (constructive rather than first-order)
we profoundly reconnect logic and computing. We
hope you see the connection.
-/

/-
Function names and applications
-/

/-
So let's get started as if we were in CS1, with
a few simple examples of functions from the Lean
libraries imported by default when Lean starts up.
Let's look at string.length, the standard function
in Lean for returning the length of any given string.
-/

#check string.length
#check string.length "CLIC!"  -- "CLIC!".length works
#eval string.length "CLIC!"   -- There's the actual length
-- Constructive Logic Is Cool!



/- In predicate logic, a function application 
can be thought of an an expression that names 
another object: it's return result. For example,
the expression (string.length "CLIC!"), serves
as another expression/name for 5. They're equal. 
-/

example : string.length "CLIC!" = 5 := rfl


/- Concepts and syntax for defining your own functions -/


/-
In the field of natural number arithmetic, one
of the fundamental functions is called successor.
In Lean it's nat.succ in Lean. It's the function
that when applied to any nat returns its successor,
the next larger nat. For example, the application
expression, (nat.succ 0), means 1, while the term,
nat.succ(nat.succ 0) means 2. (There are some
subtleties here that we'll open up later.)
-/

example : nat.succ 0 = 1 := rfl


/-
Question: What is the type of nat.succ? Figure it
out first, then you may check your answer by using 
#check.
-/


/-
So now let's define two functions using three
different syntactic approaches. 

Here are the two functions:

- sub1 : ℕ → ℕ 
    Given n, 
      case analysis:
        when n is 0, return 0, 
        when n is (nat.succ n'), return n'

In this first case, if n is not 0 then is
must be the successor of some one-smaller
number, we call it n', and that's what we
want to return to implement "subtraction of
1." Note that we also define sub1 0 to be
0.

- add2 : ℕ → ℕ 
    Given n, 
    return nat.succ(nat.succ n))
-/

/-
I will put each definition in a separate
namespace and use the same function names
throughout. For each syntactic style in
Lean, we'll implement each function and 
will show that it tests as working.
-/



/-
First, we'll see how we can define these
functions by declaring their types and then
using tactic scripts to produce correct 
values of these types: specific function 
implementations that compute and return 
the right results. It feels like you're 
just proving a theorem, but now the proof
is just a program!
-/
namespace impl_script

/-
To start off, let's declare each function
just as we'd write a logical proposition, 
and using a tactic script to implement it.
-/


def sub1 : ℕ → ℕ :=
  begin
  -- bind name to argument
  assume n,       
  -- case analysis on n
  cases n with n',
  -- case where n = 0
  exact 0,
  -- case where n = (succ n')
  exact n',
  end


def add2 : ℕ → ℕ :=
  begin
    assume n,   -- bind name to argument
    exact n+2,  -- means exactly succ(succ n)
  end


/-
Next we can show that we can apply these
functions and that they work as expected.
-/
example : sub1 0 = 0 := rfl
example : sub1 1 = 0 := rfl
example : sub1 2 = 1 := rfl
example : sub1 3 = 1 := rfl  -- bad test
example : add2 0 = 2 := rfl
example : add2 1 = 3 := rfl
example : add2 2 = 4 := rfl
example : add2 3 = 6 := rfl -- bad test

end impl_script



/-
Next we'll implement the same functions using
Lean's "pattern matching" or "by cases" syntax.
-/
namespace impl_cases

def sub1 : ℕ → ℕ 
  | 0 := 0                -- if arg is 0, then 0
  | (nat.succ n') := n'   -- otherwise one less than arg
/-
The "patterns" that we try to match with the incoming
argument are 0 and (succ n'). As we'll see soon, these
are the only two possible forms of a nat. To the right
of the := are the answers for the corresponding patterns.
So if the incoming argument is 0, 0 is returned. Lean
does pattern matching from top to bottom, returning the
specific value for the first pattern that matches.
-/

def add2 : ℕ → ℕ := 
  fun n, nat.succ (nat.succ n) 
/-
Remember how to read a function (lambda) expression.
This definition says that add2 is a function that 
takes a nat and returns a nat (that's its type) and
in particular is "the function that takes n as an
argument and returns n+2."
-/

/-
Our tests suggest our functions are working.
-/
example : sub1 0 = 0 := rfl
example : sub1 1 = 0 := rfl
example : sub1 2 = 1 := rfl
example : sub1 3 = 1 := rfl  -- bad test
example : add2 0 = 2 := rfl
example : add2 1 = 3 := rfl
example : add2 2 = 4 := rfl
example : add2 3 = 6 := rfl -- bad test

end impl_cases


/-
Finally we implement the function using a Java
style of syntax.
-/
namespace impl_cstyle

def sub1 (n : ℕ) : ℕ :=   -- first arg named to left of :
  match n with            -- match does case analysis after all
  | 0 := 0
  | (n' + 1) := n'
  end

def add2 (n : ℕ) := n+2   -- n+2 is short for succ(succ n)!

/-
Our tests suggest our functions are working yet again.
-/
example : sub1 0 = 0 := rfl
example : sub1 1 = 0 := rfl
example : sub1 2 = 1 := rfl
example : sub1 3 = 1 := rfl  -- bad test
example : add2 0 = 2 := rfl
example : add2 1 = 3 := rfl
example : add2 2 = 4 := rfl
example : add2 3 = 6 := rfl -- bad test

end impl_cstyle


/-
Next we define functions that implement 
Boolean  "and." Note that in each case we 
"pattern match" on both arguments.
-/

def my_bool_and : bool → bool → bool 
| tt tt := tt
| tt ff := ff
| ff tt := ff
| ff ff := ff

/-
Evaluation of this "cases" syntax
is, again, in top-to-bottomorder: 
if the arguments match the first 
pattern (tt tt), this function return 
the value expressed to the right of
that := (tt). If the arguments don't
match the first pattern, Lean moves
on to the next, until a match is found
and the corresponding result is returned. 
Lean will tell you if you've forgotten 
a possible combination of argument 
values. Try it by commenting out one
of the cases. 
-/


/-
A nice property of this syntax is that the 
truth table for "Boolean and" is as clear as 
day. That said, after the first of the rules, 
the rest all return false. You can use the 
"wildcard" character, _ (underscore) in Lean 
to match any value to avoid having to write
the three rules separately.
 -/

def my_bool_and2 : bool → bool → bool 
| tt tt := tt
| _ _ := ff

/-
Maybe at this point you're not sure that these
two functions have exactly the same meaning. 
Let's check that by stating the proposition 
that they return the same values for all of
the possible combinations of argument values,
and proving it. The proof is by case analysis
on the possible values of the arguments.
-/

example : 
  ∀ (b1 b2 : bool), 
    my_bool_and b1 b2 = 
    my_bool_and2 b1 b2 
  :=
begin
assume b1 b2, -- bind argument names

-- case analysis on b1 
cases b1,     

-- b1 false

-- case analysis on b2
cases b2,
-- b2 false 
apply rfl,
-- b2 true
apply rfl,

-- b1 true

-- case analysis on b2
cases b2,
-- b2 false
apply rfl,
-- b2 true
apply rfl,
end 

/-
Here are test cases
-/
example : my_bool_and tt tt = tt := rfl
example : my_bool_and tt ff = ff := rfl
example : my_bool_and ff tt = ff := rfl
example : my_bool_and ff ff = ff := rfl


/-
Functions in Lean must be "total," which means that
they must be defined to return values of the right
types for *all* possible combinations of arguments.
If you delete cases from the my_bool_and definition
you'll get a missing cases error and the following
evaluations will "block" on the undefined cases. Try
it!
-/







