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
variables {α β γ : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  

/-
ORDERING RELATIONS ON A TYPE, β 
-/

def ordering :=         reflexive r ∧ transitive r ∧ anti_symmetric r

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
def well_order := total_order r ∧ (∀ (s : set β),       -- for every
                                    ∃ (b : β), b ∈ s →  -- non-empty set s
                                      ∃ (b : β),        -- there is an element
                                        b ∈ s ∧         -- in s
                                          ∀ b' : β,     -- smaller than every other element in s 
                                            b' ∈ s →     
                                            b ≺ b')     

/-
EXAMPLE:

The requirement of asymmetry in a strict ordering
implies that no object can be related to itself. 
An example is < on the natural numbers. The only
exception is when a relation is defined on an empty
set. If you remove the condition that β be inhabited
in the next theorem, it is no longer true, insofar as
it is not true for all relations, r, over *all* types,
β. 

It's the existence of at least one value, b : β,
that enables one to derive a contradiction from the
combination of asymmetry (b cannot be related to b)
and reflexivity (b must be related to b). This is the
kind of "corner case" that can lead to severe bugs 
in code that implements such concepts. We actually
saw the false theorem posed as a problem to prove
in a professor's textbook.
-/
example : (∃ b: β, true) → asymmetric r → ¬ reflexive r :=
begin
  assume e, -- suppose β is inhabited
  assume a, -- and r is asymmetric
  assume x, -- use proof by negation 

  /- 
  Expanding the definitions of asymmetric
  and reflexive, what we are to show is
  that there is a contradiction in these
  assumptions (so r mustn't be reflexive): 
  -/
  unfold asymmetric at a,
  unfold reflexive at x,

  /-
  Let us now use w, for witness, to refer 
  to a β value that we've assumed to exist.
  -/
  cases e with w pf,
  
  /-
  By applying the reflexivity of r to w we 
  prove r w w. 
  -/
  have rww := x w,
  
  /-
  But now applying asymmetry to this fact 
  we deduce ¬r w w. 
  -/
  have c := a rww,
  
  /-
  Therein lies a contradiction.
  -/
  contradiction,

  /-
  That shows that the assumption that 
  r is reflexive must have been false.

  We've thus proved that an asymmetric
  relation over a non-empty set cannot
  be reflexive.  
-/
end

#check @well_order
#reduce @well_order

end relation
end relations
