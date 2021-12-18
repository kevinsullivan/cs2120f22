/-
# Course introduction
## Types of numbers
## Axioms and theorems
## Equality relations
## Some Lean details
-/

/-
Today proofs of mathematically and practically important
propositions can run to hundreds of thousands of lines of
logical "code," or more. Consequently, just as we have to
organize software artifacts into hierarchies of files and
definitions, so as to manage its complexity and evolution, 
so it's necessary to organize complex logical definitions
so that one can develop, undersand, verify, and use them
cost-effectively.

Similarly, just as in Python one can import definitions
from libraries that others have written, one can do the
same in Lean. Here we import definitions from a library
that defines a mathematical representation of the familiar
real numbers. You will not need to look inside the file=
in this course.

In Lean, imports must appear first in a given file (but)
for comments, which is what you're reading right now. A
comment can be enclosed by slash-dash and dash-slash, as
here, written on one line starting with dash-dash (--).
-/
import data.real.basic

/-
When we import definitions from "libraries" like this, 
whether in Python, Java, or Lean, we risk having our 
definitions of what given identifiers mean conflict with
definitions in the library. In many languages, as well 
as in Lean, namespaces provide a solution. And name, say
n, defined in a namespace, say s, will have s.n as its
full name. By enclosing all of our own definitions in a
namespace, which we'll call complogic, we avoid any such
conflicts.
-/

namespace complogic

/-
NUMBER SYSTEMS
-/

/-
Mathematicians think about operations on many kinds of objects.
In early mathematics, the objects are numbers. In later maths,
they can be polynomials, matrices, functions, symmetries, or any
manner of other "mathematical things". As we're going to see in
this class, they can even be logical propositions and proofs.

But before we get to that, let's review the concept that you
should have learned in high school: there are different types
of numbers: real, rational, and so forth. Here we review a few 
of the most familiar numerical types and notations for referring
to the sets of values that these types comprise.

ℕ: Natural numbers. The non-negative whole numbers. {0, 1, 2, ...}
ℤ: Integers: The negative, zero, and positive whole numbers. 
ℚ: Rationals: A natural number numerator and non-zero integer denominator.
ℝ: Reals: Equivalence classes of convergent sequence of rationals.
-/


/-
The following examples illustrates the use of these types in
Lean. We give definitions to the identifiers, n, z,, q, and r.
Each gets a value, "1", but these values are of different types: 
natural number, integer, rational, and real, respectively. 
-/
def n : ℕ := 1    -- 1 taken as a natural number
def z : ℤ := 1    -- 1 taken as an integer
def q : ℚ := 1/1  -- 1 as a rational number 
def r : ℝ := 1.0  -- 1 taken as a real number 

/-
We can also ask Lean to tell us the type of the value bound to
each of these identifiers using the #check command.
-/
#check n 
#check z
#check q 
#check r 

/-
We can also reduce any given identifier to the value to 
which it is bound, using the #reduce command in Lean. 
-/

#reduce n
#reduce z
#reduce q

/-
At 
least we can try. Real numbers in both mathematics and 
therefore in Lean are represented by ("equivalence classes"
of) infinite sequences of rational numbers that "converge"
to some point. They cannot be used in computations. They
cannot be printed out. If you uncomment the fourth line in
what follows, Lean will get itself into a state in which 
it's trying (indicated by an orange line in the VS Code
IDE) but not making any progress.
-/
--#reduce r

/-
But let's start with something really simple. The number, 1. Ok,
it's actually not that simple, because 1 can be interpreted as 
denoting a natural number, integer, real number, rational number,
identity matrix, identity function, identity element of a group,
or any manner (again) of "mathematical thingy". If Lean sees a 
bare numeral, 1, it interprets it as the natural number, 1. It
is possible to force many other interpretations however, as the
following examples show.

As you read the code, remember the following.

Examples:

Natural numbers:  0, 3, 11, 29
Integers:         -29, 0, 3, 11
Rationals:        1/2, -3/4, 23/7
Reals:            0.000..., .333..., 3.1415...
Irrationals:      3.1415..., e, sqrt 2
-/

def m := 1        -- 1 inferred to be a natural number (built into Lean)
def n : ℕ := 1    -- 1 specified to be a natural number (non-negative whole number)
def z : ℤ := 1    -- 1 as an integer (negative or non-negative whole number)
def r : ℝ := 1.0  -- 1 as a real number (infinite decimal sequence)
def q : ℚ := 1/1  -- 1 as a rational number (fraction)
 
/-
Each proceeding line of code has the following elements
- def: a keyword, binds the given identifer to the given value
- n, m, z, r, q: identifiers, a.k.a., variables or variable names
- : T, where T is ℕ, ℤ, ℝ, or ℚ: specifies the *type* of the value
- := 1.0: specifies the value, 1.0, to be bound to the identifier 
-/

/-
The same definitions could be written as follows, allowing Lean
to fill in type information that it can infer from the way in
which the values are given.
-/

def m' := 1           -- Lean assumes 1 is a natural number (built into Lean)
def n' := (1 : ℕ)     -- 1 as a natural number (non-negative whole number)
def z' := (1 : ℤ)     -- 1 as an integer (negative or non-negative whole number)
def r' := (1.0 : ℝ)   -- 1 as a real number (infinite decimal sequence)
def q' := 1/1         -- Here Lean infers 1/1 is rational number (fraction)


/-
AXIOMS, PROPOSITIONS, PROOFS
-/

/-
Let's again talk about propositions and 
proofs involving "equality" propositions,
such as the proposition that 1 = 1. We
all *know* intuitively that 1 = 1, but
how would you prove it, given that it's
not an axiom of ordinary predicate logic?


Without getting into the weeds, suffice
it to say that the standard Lean Prover
libraries define equality pretty much as 
we've discussed here: with an axiom in 
the form of a universal generaliztion: 
∀ {T : Type} (t : T), t = t.

In English, this says, "if you give me 
*any* Type, T, and any object, t, of that
type, I will return you a proof of the 
proposition, t = t. The existence of such
a proof, in turn, justifies the judgment 
that the proposition, 1 = 1, is *true*.  

Let's take another look at the axiom that
let's us *deduce* the *theorem* that 1 = 1.
Here it is: ∀ {T : Type} (t : T), t = t.
What that means is that if I choose any
type, T, say T = ℕ, and any value of that
type, say t = (1 : ℕ), then I should be 
able to apply the axiom to the argument
values, ℕ and 1, to get back a *proof* of
the proposition, 1 = 1. 

Indeed, that's just how it works, as the
follow example shows formally (in Lean).
-/

example : 1 = 1 := 
  eq.refl 1   -- Lean inferns T = ℕ from 1

/-
Yay! We just constructed a formal proof: a
mathematical object that certifies that 1=1. 
It might not be super-impressive that Lean 
rejects "eq.refl 2" as a suitable proof (try
it, and don't fail to read the entire error
message when you hover your cursor over the
red squiggle!); but the principle extends to 
commplex proofs of profound propositions. 

Nice: you've not only constructed a formal 
proof object but you have a "high assurance" 
check that the proof itself is correct, in
that Lean actually accepts that it's correct. 
*That* is what Lean is really for: not just 
for formalizing mathematics and logic, but 
for checking that proofs *truly* prove what
they claim to prove. 
-/

/-
Of course, if formal proofs came without 
costs, we'd all be using them. The benefit 
of a *natural language* "proof description"
(written in, say, English, but in a highly
mathematical style) is that it's easier for
people to follow, often because details can
be elided on the assumption that the reader
will know from context what is meant. 

In this case at hand, you could give a proof, 
of the proposition, 1 = 1, as follows:

Proof: By the reflexive property of equality
(applied to the particular value, 1). QED." 

If you and your audience both understand that
you're *applying* the universal generalization
given as an axiom to suitable values, then you
can just leave out the parenthetical expression.
How much detail to put in a proof description
is a matter of style and of a willingness to
make your readers fill in the missing details. 

The QED, by the way, is short for quod est 
demonstratum, Latin for "it is shown." It is
a kind of traditional punctuation for natural
language proof descriptions that signals that 
the proof is complete.

The downside of using natural language proof
descriptions in lieu of formal proof objects
is that when things get complex, it can be 
nearly impossible to tell whether a proof in
natural language is correct or not. In hard
cases, it can require years of work by world
experts to decide whether a proof is correct
or faulty.

In this class, we will insist, because all
mathematicians do, that your propositions 
be fully formal, i.e., syntactically correct
by the grammatical rules of predicate logic, 
as enforced by Lean. We will expose you to 
formal proofs to the extent that we believe
that doing so will help you to understand
how to write quasi-formal proof descriptions.

Quasi-formal proofs are what most people use
today, including instructors for follow-on CS
courses. But there are now thriving communities
in both mathematics and computer science that
are aggressively pursuing the formalization,
and the *computerization* of logic and proof.
The community around Lean is most interested
in formalizing mathematics for mathematicians.
Other critically important applications of 
Lean and similar "proof assistants" arise in
relation to the definition of programming
languages, and in the formal (mathematical)
specification and trustworthy and automated 
correctness checking of computer programs.
-/

/-
If you're getting the feeling that we are
pointing you a little bit to a computational
understand of what it means to construct or
to use proofs, you're right. To make the point
clearer, let's write our own proof-returning 
function@ We'll call it gimme_a_proof. It 
will take two arguments, a type, T, and a 
value, t, of that type; and it will return 
a proof of t = t, on the basis of which we
can render the judgment that t = t is *true*.
-/

def gimme_a_proof   -- function name
    (T : Type)      -- first argument
    (t : T)         -- second argument
    : t = t         -- return "type" 
    := eq.refl t    -- implementation

/-
Let's decode that. We're defining a function
called gimme_a_proof that takes T and t as 
its arguments and promises to return a value 
of type t = t (a proof of this proposition).
The way that it upholds this promise is by
*applying* eq.refl to t, whatever it is, to 
construct a proof of t = t. That proof is the
result and return value of this function. 
-/

/-
Now that we've got this function defined, 
we can apply *it* to arguments to have it
construct values that constitute proofs of 
t = t. If you hover over #reduce in the 
following Lean commands, Lean will report
to you the results of applying the function
to arguments of various numerical types.
Remember when reading the outputs that
"eq.refl x" *is* an object that serves 
as a proof of x = x
-/

#reduce gimme_a_proof ℕ 9
#reduce gimme_a_proof bool tt
#reduce gimme_a_proof ℚ 1
#reduce gimme_a_proof ℤ (-3)

/-
That wraps up this review (and extension)
of our last lecture. Now for the quiz.
-/



/-++++++++++
EXERCISES #1.
Give a quasi-formal English language "proof" 
of the proposition that 2 = 2.

Theorem: 2 = 2.
Proof: [your answer here]

-/


/-++++++++++
EXERCISE #2.
Give, below, a formal statement and proof of 
the proposition, 2 = 2. (See above for a good
example to follow!)
-/

-- answer here

example : 2 = 2 := @eq.refl ℕ 2


/-
EXERCISE #3.
Identify what form of reasoning is being used 
in each of the following made-up stories. Just
give a one-word answer for each.

A. Every time the bell has rung, I've gotten a
nugget. The bell just rung, so I'm gonna get a
nugget! (Dogs usually say "gonna," by the way).

answer: 

B. The "clone repo into container" command did
nothing. That was clearly wrong. I search around
on the World Wide Web and notice someone saying
something about that VSCode command needed to 
have git installed. Ah ha, I thought. That could
be it. I'll do the obvious experiment and install
git and see if it works. (It did, by the way.)

answer: 

C. It's true that it's raining, and it's true
that the streets are wet, so it must be true 
that "it's raining *and* the streets are wet."

answer: 
-/

end complogic