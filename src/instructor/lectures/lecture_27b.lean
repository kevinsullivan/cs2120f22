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

#check @function        -- property of a relation

/-
The same vocabulary applies to functions as to
relations, as functions are just a special case
of relations.

In particular, a function is not just a set of pairs
but *also* has an associated domain of definition (α)
and co-domain (β). The set of pairs of a function, 
just as with any relation, is a subset of α × β. 

We can also say that the set of pairs of a relation 
is either a subset of α × β or that the set of pairs
is an element of the powerset of α × β. 

  - let r ⊆ α × β be a relation/function from α → β  
  - let r ∈ 𝒫 (α × β) be a relation/function, α → β 

Be sure you see that these are equivalent statements!
The main point is that in addition to a set of pairs a
function (or relation) also has a domain of definition
and a co-domain. You will see why shortly.
-/

/- RELATION "DEFINED" FOR A VALUE

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

/- TOTAL vs PARTIAL FUNCTION

Property: We say that a function is "total" if it is
defined for every value in its domain. Note that this
usage of the word "total" is completely distinct from
what we learned earlier for relations in general. It's
thus better to use "strongly connected" for relations
in which every object is involved in a relation one way 
or the other, and to use total to refer to a function 
that is defined on every element of its domain. So, for 
a total function, r, domain_of_definition r = domain r.
-/

def total_function := function r ∧ ∀ (a : α), defined r a
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

/- SURJECTIVE FUNCTION

A function that covers its codomain (where every value in 
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
-- homework
end

/-
Which of the following functions are surjective?

- y = log x, viewed as a function from ℝ → ℝ⁺
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
  ∀ {x y : α} {z : β}, r x z → r y z → x = y
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
EXERCISE: Prove that the inverse of a 
bijective function is a function.
-/

example : bijective r → function (inverse r) :=
begin
end 


/-
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

/-
I will not test you on your ability to reason about injective
and surjective partial functions, except maybe as extra credit
questions; but it's nice in any case to understand these clear
and beautiful definitions. And to know that you'd also have no
problem providing these as properties of any partial function.
-/

end functions
end relations

