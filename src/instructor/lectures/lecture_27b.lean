import .lecture_26
import data.set

namespace relations

section functions

variables {α β γ : Type} (r : α → β → Prop)
local infix `≺`:50 := r

/-
SINGLE-VALUED BINARY RELATION
-/

def single_valued := 
  ∀ {x : α} {y z : β}, r x y → r x z → y = z 

#check @single_valued   -- property of a relation


/-
Exercises: Which of the following are single-valued?
- r = {(0,1), (0,2)}
- r = {(1,0), (2,0)}
- the unit circle on ℝ 
- r = {(-1,0), (0,-1), (1,0), (0,1)}
- y = x^2
- x = y^2
- y = + / - square root x
- f(x) = 3x+1
- y = sin x
- x = sin y
-/

/- FUNCTION

A single-valued binary relation is also called a 
function (sometimes a functional binary relation).
-/
def function := single_valued r

/-
One possible property of a relation, r, is the 
property of being a function, i.e., of r being
single-valued. Single-valuedness is a predicate
on relations. (This idea is isn't definable in
first order predicate logic.)
-/
#check @function  

/-
The same vocabulary applies to functions as to
relations, as functions are just special cases
(single-valued) of otherwise arbitrary binary 
relations.

As with any relation, for example, a function 
has a domain, α, a domain of definition, and a
co-domain, β. As with any relation, the set of 
pairs of a function (that we're specifying) is
is some subset of α × β; or equivalently it is
in the powerset of α × β. 

When you want to express the idea that you have 
an arbitrary relation (possible a function) from
α to β, you may write either of the following:

  - let r ⊆ α × β be any relation from α → β  
  - let r ∈ 𝒫 (α × β) be any relation, α → β 
  - let r : α → β be any binary relation

Be sure you see that these are equivalent 
statements! A key point is that in addition 
to a set of pairs a function (or relation) 
has a domain of definition and a co-domain.
Keeping track of exactly how a set of pairs
relates to its domain and codomain sets is
essential.
-/

/- FOR A RELATION TO BE "DEFINED" FOR A VALUE

Property: We say that a function is "defined" for some
value, (a : α), if there is some (b : β), such that the
pair, (a,b) is "in" r, i.e., (r a b) is true.
-/

def defined (a : α) := ∃ (b : β), r a b

/-
Examples: Which is partial, which is total?

- the positive square root function for x ∈ ℝ (dom def)
- the positive square root function for x ∈ ℝ, x ≥ 0 
-/


/- THE TOTAL vs PARTIAL FUNCTION DICHOTOMY

Property: We say that a function is "total" if it is
defined for every value in its domain. Note that this
usage of the word "total" is completely distinct from
what we learned earlier for relations in general. It's
thus better to use "strongly connected" for relations
to mean every object is related to another in at least
one direction, and to use total to refer to a function 
that is defined on every element of its domain. 
-/

def total_function := function r ∧ ∀ (a : α), defined r a

/-
At this point we expect that for  a total function, r, 
dom_of_def r = domain r. At one key juncture you use
the axiom of set extensionality to convert the goal 
as an equality into that goal as a bi-implication.
After that it's basic predicate logical reasoning,
rather than more reasoning in set theory terms. 
-/

example : total_function r → dom_of_def r = dom r :=
begin
  assume total_r,
  cases total_r with func_r defall,
  unfold dom_of_def,
  unfold dom,
  apply set.ext,
  assume x,
  split,

  -- forwards
  assume h,
  unfold defined at defall,
  unfold defined at defall,
  -- goal completed
  
  -- backwards
  assume h,
  exact defall x,

end

/-
With that proof down as an example, we return to complete
our list of properties of functions: 
  - total
  - partial
  - strictly partial
Here are the definitions for the remaning two.
-/

def strictly_partial_fun := function r ∧ ¬total_function r
def partial_function := function r -- includes total funs

/-
Mathematicians generally consider the set of partial
functions to include the total functions. We will use
the term "strictly partial" function to mean a function,
f, that is not total, where dom_of_def f ⊊ dom f. (Be
sure you see that the subset symbol here means subset
but not equal. That's what the slash through the bottom
line in the symbol means: strict subset.)
-/

/- SURJECTIVE FUNCTIONS

A function that "covers" its codomain (where every value in 
the codomain is an "output" for some value in its domain) 
is said to map its domain *onto* its entire codomain. 
Mathematicians will say that such a function is "onto," 
or "surjective." 
-/

def surjective := 
  total_function r ∧  
  ∀ (b : β), ∃ a : α, r a b

/-
Should this be true?
-/

example : 
  surjective r → 
  image_set r (dom r) = { b : β | true } :=
begin
-- homework (on your own ungraded but please do it!)
end

/-
Which of the following functions are surjective?

- y = log x, viewed as a function from ℝ → ℝ⁺

As written, the question is, um, tricky. Let's 
analyze it. Then we'll give simpler questions.

First a little background on logarithmic and
exponential functions. Simply put, exponentiation
raises a base to an exponent to produce an output,
while the logarithm takes and converts it into 
the exponent to which the base is raised to give
the input. 

From basic algebra, the log (base 10) function,
y = log(x), is defined for any positive real, x,
and is equal to the exponent to which the base
(here 10) must be raised to produce x. Therefore
as usually defined its domain of definition is
the *positive reals* and its co-domain is (*all
of*) the reals.

Now consider the question again. The domain of
definition of log is the positive reals, so if
we expand the domain to all the reals, then the
resulting function becomes partial. On the other
side, if we restrict the range to the positive
reals, then we are excluding from the function
all those values in the interval (0,1) from the
input side in order to restrict the output to
values greater than 0. 

Self homework: Graph this function. 

- λ x, log x : ℝ+ → ℝ, bijective? 
- y = x^2, viewed as a function from ℝ → ℝ 
- y = x, viewed as a function from ℝ → ℝ
- y = sin x, viewed as a function from ℝ → ℝ
- y = sin x, as a function from ℝ to [-1,1] ∈ ℝ

-/

/- INJECTIVE FUNCTION

We have seen that for a relation to be a function, it 
cannot be "one-to-many" (some x value is associated
with more than one y value). On the other hand, it is
possible for a function to associate many x values 
with a single y value. There can be no fan-out from 
x/domain values to y/codomain values, but there can
be fan-in from x to y values.

Which is the following functions exhibits "fan-in",
with different x values associated with the same y
values?

y = x
y = sin x
x = 1 (trick question)
y = 1
y = x^2 on ℝ 
y = x^2 on ℝ⁺ (the positive reals)
-/

def injective := 
  total_function r ∧ 
  ∀ {x y : α} {z : β}, 
    r x z → r y z → x = y
/-
We will often want to know that a function does not
map multiple x values to the same y value. Example:
in a company, we will very like want a function that 
maps each employee to an employee ID number *unique*
to that employee. Rather than being "many to one" we
call such a function "one-to-one." We also say that
such a function has the property of being *injective*.
-/

/-
We will often want to know that a function does not
map multiple x values to the same y value. Example:
in a company, we will very like want a function that 
maps each employee to an employee ID number *unique*
to that employee. Rather than being "many to one" we
call such a function "one-to-one." We also say that
such a function has the property of being *injective*.
There is yet another way to understand the concept.
-/


/- BIJECTIVE FUNCTIONS
-/

/-
Finally, a function is called one-to-one and onto, or
*bijective* if it is both surjective and injective. In
this case, it has to map every element of its domain
-/

def bijective := surjective r ∧ injective r

/-
An essential property of any bijective relation is that 
it puts the elements of the domain and codomain into a
one-to-one correspondence. 

That we've assumed that a function is total is important
here. Here's a counterexample: consider the relation from
dom = {1,2,3} to codom = {A, B} with r = {(1,A), (2,B)}.
This function is injective and surjective but it clearly
does not establish a 1-1 correspondence. 

We can define what it means for a strictly partial function
to be surjective or injective (we don't do it formally here).
We say that a partial function is surjective or injective if
its domain restriction to its domain of definition (making it
total) meets the definitions given above. 

Note that our use of the term, one-to-one, here is
completely distinct from its use in the definition of 
an injective function. An injective function is said
to be "one-to-one" in the sense that it's not many to
one: you can't have f(x) = k and f(y)=k where x ≠ y. 
A one-to-one correspondence *between two sets*, on the 
other hand, is a pairing of elements that associates
each element of one set with a unique single element
of the other set, and vice versa.
-/

/-
Question: Is the inverse of a function always a function.
Think about the function, y = x^2. What is its inverse?
Is it's inverse a function? There's your answer.

A critical property of a bijective function, on the other
hand, is that its inverse is also a bijective function. It
is easy to see: just reverse the "arrows" in a one-to-one
correspondence between two sets. A function who inverse 
is a function is said to be invertible (as a function, as 
every relation has and inverse that is again a relation). 
-/

/-
EXERCISE #1: Prove that the inverse of a 
bijective function is a function. Ok, yes, 
we will work this one out for you! But you
should really read and understand it. Then
the rest shouldn't be too bad.
-/

example : bijective r → function (inverse r) :=
begin
  /-
    Assume hypothesis
  -/
  assume r_bij,

  /-
  Unfold definitions and, from definitions,
  deduce all the basic facts we'll have to
  work with.
  -/
  cases r_bij with r_sur r_inj,
  cases r_inj with r_tot r_one_to_one,
  cases r_sur with r_tot r_onto,
  unfold total_function at r_tot, 
  cases r_tot with r_fun alldef,
  unfold function at r_fun,
  unfold single_valued at r_fun,
  unfold defined at alldef,

  /-
  What remains to be shown is that the
  inverse of r is function. Expanding 
  the definition of function, that means
  r inverse is single-valued. Let's see. 
  -/
  unfold function,
  unfold single_valued,
  /-
  To show that r inverse (mapping β values
  back to α values) r is single-valued, 
  assume that b is some value of type β 
  (in the codomain of r) and show that if 
  r inverse maps b is mapped to both a1 and 
  a2 then a1 = a2.
  -/
  assume b a1 a2 irba1 irba2,
  /-
  Key insight: (inverse r) b a means r a b. 
  In other words, r b a is in r inverse (it
  contains the pair (b, a)) if and only if 
  (a, b) is in r, i.e., r a b.
  -/
  unfold inverse at irba1 irba2,
  /-
  With those pairs now turned around, by the 
  injectivity of r, we're there!
  -/
  apply r_one_to_one irba1 irba2,
end 

/-
Just to set expectations: The reality is that
I explored numerous ways of writing this proof.
Often a first proof will be confusing, messy,
etc. Most proofs of theorems you see in most
mathematics books are gems, polished in their
presentations by generations of mathematicians.
It took me a little while to get to this proof
script and the sequence of reasoning steps and
intermediate proof states it traverses. 
-/


/- INJECTIVE AND SURJECTIVE *PARTIAL* FUNCTIONS

Okay, we actually are now able to to define just
what is means for a *partial* function to be
injective, surjective, bijective, which is that 
it is so when its domain is restricted to its 
domain of definition, rendering it total (at 
which point the preceding definition applies). 
-/

def injectivep := function r ∧ injective (dom_res r (dom_of_def r))
def surjectivep := function r ∧ surjective (dom_res r (dom_of_def r))
def bijectivep := function r ∧ bijective (dom_res r (dom_of_def r))




-- EXERCISE #2: Prove that the inverse of a bijective function is bijective.
example : bijective r → bijective (inverse r) :=
begin
end


/-
EXERCISE #3: Prove that the inverse of the inverse of a bijective
function is that function.
-/
example : bijective r → (r = inverse (inverse r)) :=
begin
end

/-
EXERCISE  #4: Formally state and prove that every injective function 
has a *function* as an inverse.
-/
example : injective r → function (inverse r) :=
  _ -- hint: remember recent work


/-
EXERCISE #5. Is bijectivity transitive? In other words, if the
relations, s and r, are both bijective, then is the
composition, s after r, also always bijective? Now
we'll see.
-/

open relations    -- for definition of composition

/-
Check the following proposition. True? prove it for all.
False? Present a counterexample.
-/
def bij_trans (s : β → γ → Prop)  (r : α → β → Prop) :
  bijective r → bijective s → bijective (composition s r) := 
begin
assume br bs,
split,
-- surjective
unfold surjective,
split,
  -- compoisition total
  unfold total_function,
  split,
   -- composition is a function
   unfold function single_valued,
   assume x y z srxy srxz,
   unfold bijective at br bs,
   cases bs,
   cases br,
   unfold composition at srxy srxz,
   unfold surjective at  bs_left,
   unfold surjective at  br_left,
   unfold injective at br_right bs_right,
   cases bs_left,
   cases br_left,
   cases bs_right,
   cases br_right,
   -- composition is defined for all α 
-- injective
end

/-
In general, an operation (such as inverse, here) that, 
when applied twice, is the identity, is said to be an
involution. Relational inverse on bijective functions
is involutive in this sense.

A visualization: each green ball here goes to a red
ball there and the inverse takes each red ball right
back to the green ball from which it came, leaving
the original green ball as the end result, as well.
An identity function.
-/

end functions
end relations

