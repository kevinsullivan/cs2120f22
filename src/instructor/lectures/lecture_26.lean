import .lecture_25
import data.set

/-
Operations on relations
-/

/-
We now change our attention to binary relations
more generally: not just from β → β but between
different types, α and β. Not the change in the
type of r as defined here.
-/
variables {α β γ : Type} (r : α → β → Prop)
local infix `≺`:50 := r

/-
We will call the set of all α values the "domain"
of the relation r, and we will call the set of all 
β values the "codomain" of r. Now the (a, b) pairs 
of r represent the pairs of values for which r a b 
is true. You can visualized such an (a, b) pair as
an arrow from a in the domain to b in the codomain.

Not every value in α needs to be present in the 
set of "a" values that appear as first elements
in the pairs of r. The subset of a values that 
do appear in the first position of some pair in
r is what we will call the domain of definition
of the relation. 

The set of b values that appear in the second
positions in all such pairs of r is the set we
will call the *range* of the r. 

Be able to write the formal definitions, which 
we present next, from your memory and even 
more from understanding of what they mean. If 
you understand, then you should be able to write
the formal definitions without having memorized
them.
-/

/-
We begin with sets involved in any relation, 
r : α → β → Prop. For simplicity we'll assume
that the domain set in examples that follow is 
specified by the type α, and that the co-domain
set is specificed by the β type.
-/
def dom (r : α → β → Prop) : set α := { a : α | true } 
def codom (r : α → β → Prop) : set β := { b : β | true }

def dom_of_def (r : α → β → Prop) : set α := { a : α | ∃ b, r a b }
def range (r : α → β → Prop) : set β := { b : β | ∃ (a : α), r a b  }


-- EXAMPLE
/-
Let R by the relation between natural numbers
and strings of those lengths. E.g., (5, "hello")
would by in the relation because 5 is the length
of the string, "hello."
-/
def R : ℕ → string → Prop := λ n s, n = s.length
#check dom R
#reduce dom R
#check codom R
#reduce codom R -- what set?
#check dom_of_def R
#reduce dom_of_def R    -- a set, right?
#check range R
#reduce range R     -- a set, right?


/- RESTRICTION OF A RELATION  

It will often be useful to consider the
subrelation obtained by restricting the
domain of a relation to elements of a 
set, s. 

If a relation relates three cats, c1, c2, 
and c3, to their ages, say a1, a2 and a3,
respectively, then restricting the domain
of r to the set, s = {c1, c3}, would give
the relation associating c1 and c3 with
corresponding ages, but there would be no
(c2, a2) pair in the restricted relation
because c2 ∉ s. An analogous definition 
gives us the range restriction of r to a
set, s. 
-/

/-
Note that these operations take relations and
sets as arguments and "return" new relations
(again represented as two_place predicates).

Of course, these are logical specifications, 
not programs, so they don't really compute 
anything at all, but they do provide formal
"specifications" of useful programs that can
be implemented. Indeed, the set of relational
concepts in this file is really at the heart
of the relational specification of programs.
-/
def dom_res 
  (r : α → β → Prop) 
  (s : set α) : 
  α → β → Prop := 
λ a b, a ∈ s ∧ r a b   

def ran_res 
  (r : α → β → Prop) 
  (s : set β) : 
  α → β → Prop := 
_                       -- homework


/-
In a relation in general, an α value can have zero,
one, or more corresponding β values. As a nice example,
consider the binary relation on real numbers defined
by x^2 + y^2 = 1^2. From basic algebra, recall that,
by the pythagorean theorem, this relation comprises
all of the x-y pairs in the unit circle. It's the
set of real number (x,y) pairs for which x^2+y^2=1.

Now where x is zero, as an example, there is not one
but there are two corresponding y values: -1 and 1.
That's fine because a relation is *any* subset of
the set of all α-β pairs. In particular, the "circle"
relation contains both (0,1) and (0,-1). Each pair
satisfies the specification, that x^2+y^2=1. Be sure
you see that this simple algebraic claim is correct.

If we think of "applying" a relation to a value, then,
we have to get back not a single value, in general, but
a set of values that could, in general, be empty, be
a singleton set, or have more than one value. In our
case here where r is the unit circle relation, what
should we expect as the value of (r 0)?

Yes, it's the set { 1, -1 }. We will this result set
the "image" of 0 under r. I guess you can think of r
as being like a bright light shining on 0 from the
left and being blocked from projecting through to the
corresponding β values except for where that 0 is.
What gets illuminated in this case is the set of β 
values, { 1, -1 }.

We can then easily extend this concept to the image
of a set of α values.

Note that the folloowing operations take a relation
and a value and return a set of values.
-/

-- image of an "argument" value under r
def image_val (a : α) : set β :=
{ b : β | a ≺ b } 

-- image of a set, s, of arguments, under r
def image_set (s : set α) : set β :=
{ b : β | ∃ a : α, a ∈ s ∧ a ≺ b }


/- HOMEWORK
Define the concepts of the *pre-image* of a
value of type β or of a set of such values.
-/

/-
Here's another operation that takes a relation
and returns a relation: namely the same as the
original but with all the pair arrows reversed.
-/
-- inverse of r
def inverse : β → α → Prop :=
λ (b : β) (a : α), r a b


/-
Finally we have this beautiful operation that
takes two relations as arguments and glues them
together into a new end-to-end relation: the
*composition* of s with r. The result of applying
this relation to an (a : α) is the (c : γ) that
is obtained by applying the relation s to the 
result of applying the relation r to a. We can
thus call the resulting relation "s after r."
-/
def composition (s : β → γ → Prop) (r : α → β → Prop):=
  λ a c, (∃ b, s b c ∧ r a b)

#check @composition

/-
EXTENDED EXAMPLE
-/

/- 
Let square be the binary relation that 
associates natural numbers with their 
squares.
-/
def square := (λ a b : ℕ, b = a * a)

/- 
Let incr be the binary relation that 
associates natural numbers with their 
successors (one more).
-/
def incr := (λ b c : ℕ, c = b + 1)

/-
Let square_after_incr be the composition
of square and incr, namely the composed
function "square after increment" (where
incr is short for increment).
-/
def square_after_incr := composition square incr

/-
Think of square_after_incr as specifying a 
function where an argument, a, enters from the
right of incr, moves left through incr, being
increased by 1 in the process, then moves left
again through through square, being squared in
that process. So this relation associates any
natural number with the square of its successor.
-/

#check square             -- binary relation on ℕ 
#check incr               -- binary relation on ℕ
#check square_after_incr  -- binary relation on ℕ
#reduce square_after_incr -- λ (a c : ℕ), ∃ (b : ℕ), 
                          --  c = b.mul b ∧ b = a.succ
                          -- another relation on ℕ 

/-
Of course there's no computation actually going
on here. Rather, the composed relation is again
just specified logically.
-/

#reduce square_after_incr
-- λ (a c : ℕ), ∃ (b : ℕ), c = b.mul b ∧ b = a.succ

/-
State and prove the conjecture that (3,16) 
is "in" the square_after_incr relation. Then
show that (3,15) is not in this relation.
-/
example : square_after_incr 3 16 :=
begin
unfold square_after_incr square incr composition,
apply exists.intro 4,
split,
repeat { exact rfl },
end

/-
Proof (English).

Unfolding all of the definitions we see we are
to prove ∃ (b : ℕ), 16 = b * b ∧ b = 3 + 1. Let
b = 4, split the conjunction, and prove each side
by simplifying and by the reflexivity of equality. 
QED.
-/

example : ¬ square_after_incr 3 15 :=
begin
  assume h,
  unfold square_after_incr square incr composition at h,
  cases h with w pf,
  cases pf with sq inc,
  rw inc at sq,
  cases sq,   -- contradiction
end

/-
We'll use proof by negation, assuming that 
(3,15) is in square_after_incr and showing
that this leads to a contriction, i.e., by
applying negation introduction. 

Expanding all the definitions, we are to show
that ∃ (b : ℕ), 15 = b * b ∧ b = 3 + 1 leads
to a contradiction. By ∃ elimination, we have
a witness w and that 15 = w * w and w = 3 + 1.
Rewriting w in the first equality using the
second, we have 15 = (3 + 1) * (3 + 1). This
assumption is inconsent, as proven by case
analysis on the possible forms of a proof of
such an equality, of which there are none to
consider.
-/

/-
Alternative:
We'll use proof by negation. Assume (3,15) 
∈ square_after_incr. Expanding definitions, 
we need to show that assuming that 
∃ (b : ℕ), 15 = b * b ∧ b = 3 + 1 leads to
a contradiction. Clearly b must be 4 and 
that leads to the absurd conclusion that
15 = 16. The original assumption that (3,15) 
∈ square_after_incr must have been wrong 
thus (3,15) ∉ square_after_incr.
QED.
-/

/-
Proof by negation: What we're asked to show
is that ∃ (b : ℕ), 15 = b * b ∧ b = 3 + 1.
Clearly there is no such b. QED.
-/
