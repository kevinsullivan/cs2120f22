import .lecture_24

/-
BASIC SETUP
-/
namespace relations
section relation

/-
Define relation, r, as two-place predicate on 
a type, β, with notation, x ≺ y, for (r x y). 
-/
variables {β : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  

/-
ORDERING RELATIONS ON A TYPE, β 
-/

def ordering := 
  reflexive r ∧ transitive r ∧ anti_symmetric r

/-
An ordering is any relation in which (1) every
object a is related to itself (think "less then
or equal" to); (2) if an object a is "less than
or equal to" an object b, and b is less than or
equal to c, then a is "less than or equal to c",
and (3) crucially, if a is "less than or equal
to b" then the only way b can also be "less than
or equal to a is if and and b are in fact equal."
It's the anti_symmetry that prevents the case in
which you have both a ≺ b and b ≺ a where a ≠ b.
To have such a state would undermine the notion
that the relation puts the objects in a definite
"order." While the concept of anti-symmetry might
at first have seemed a but abstract, you can see
here how crucial it is to defining concepts that
we really care about, such as the concept of an
ordering.  
-/

def partial_order :=    ordering r ∧ ¬strongly_connected r
def total_order :=      ordering r ∧ strongly_connected r
def strict_ordering :=  asymmetric r ∧ transitive r

/-
EXAMPLE:
The requirement of asymmetry in a strict ordering
implies that no object can be related to itself. 
An example is < on the natural numbers. The only
exception is when a relation is defined on an empty
set. If you remove the condition that β be inhabited
in the next theorem, it is no longer true, insofar as
it's not true for all relations, r, on all types, β. 

It's the existence of at least one value, b : β,
that enables one to derive a contradiction from the
combination of asymmetry (b cannot be related to b)
and reflexivity (b must be related to b). This is the
kind of "corner case" that can easily lead to serious
conceptual (not coding) errors in software design as
well as in mathematics, per se.
-/

/-
The next concept of importance, especially when it
comes to proofs of termination of recursive functions,
is that of a well order, aka wellorder, wellordering.
It's a combination of a total order (like ≤ but not
⊆) and this property that in any set of values there
is always a least element.

The nats are well ordered under ≤. Intuitively, every
possible set of natural numbers (even an infinite set)
will have a least element. The very least element of 
all is 0, so no matter what set one picks, it will have
either zero or some direct or indirect successor of 0
as its least element.

The integers, on the other hand are not well ordered 
under ≤. Think about and be sure you understand why. 
If you get stuck thinking about this, go back to the
definition of well-order and revisit the idea that 
every possible set of β values will have a least
element. What goes wrong when we pick ℤ rather than
ℕ under ≤?

This concept is important in enabling one to prove
that recursive functions are well founded: that no
matter what finite input they are given they will
stop running after some finite number of steps: i.e.,
they won't call themselves recursively without end.

The idea will be to show that each recursive call 
that a function makes is given an argument value 
that is "smaller" than the one that the function
received in the first place. As long as each time
an argument from a well ordered set is passed it 
is smaller than the one that was received, then in
some finite number of recursive calls, a "least"
argument value will be encountered for which no
yet "smaller" value exits. Such a value is called
a "base case" in a recursive definition. We will
see more about this shortly.  
-/
def well_order := total_order r ∧ (∀ (s : set β),       -- for every
                                    ∃ (b : β), b ∈ s →  -- non-empty set s
                                      ∃ (b : β),        -- there is an element
                                        b ∈ s ∧         -- in s
                                          ∀ b' : β,     -- smaller than any other value in s 
                                            b' ∈ s →     
                                            b ≺ b')     

/-
At this point in this course, we do expect you
to be able to read and make good sense of this
definition and others of this complexity. 
-/

end relation
end relations
