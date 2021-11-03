import .lecture_22
import data.set

/-
ADDITIONAL PROPERTIES OF RELATIONS
-/

namespace relations

section relation

/-
Define relation, r, as two-place predicate on 
a type, β, with notation, x ≺ y, for (r x y). 
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  

-- special relations on an arbitrary type, α 
def empty_relation := λ a₁ a₂ : α, false
def full_relation := λ a₁ a₂ : α, true
def id_relation :=  λ a₁ a₂ : α, a₁ = a₂ 

-- Analog of the subset relation but now on binary relations
-- Note: subrelation is a binary relation on binary relations
def subrelation (q r : β → β → Prop) := ∀ ⦃x y⦄, q x y → r x y

/-
Commonly employed properties of relations
-/

def total := ∀ x y, x ≺ y ∨ y ≺ x
/-
Note: we will use "total" later to refer to a different
property of relations that also satisfy the constraints
needed to be "functions."  
-/

def anti_reflexive := ∀ x, ¬ x ≺ x
def irreflexive := anti_reflexive r -- sometimes used
def anti_symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x

/- 
The transitive closure of a relation, r, is another 
relation, r', where r' is the smallest relation that
both contains r and is transitive. In other words, it
is r "completed" with the addition, only as necessary,
of edges needed to make the result transitive. 

In plain English, if there's a "path" of pairs between 
two values, a and c, e.g., by way of b where (a,b) and 
(b,c) are in the relation, then (a,c) will also be in
the relation, i.e., the direct connection, (a,c), will
also be in the relation. 

The following formal definition is not one that I 
expect you to understand immediately, as we have not
yet introduced iductive definitions, of which this is
an example. But you can just read it as definining
the introduction rules, base and trans, for proving
one relation is the transitive closure of another, r.

The first rule says that if any two objects, a and b,
are related in r, then they are also related in tc r
(the transitive closure of r). The second rule says 
that if objects a and b are related in (tc r) and b
and c are related in (tc r) then a and c must also 
be related in r. For any length-2 "path" from a to c
(via b), then there's a direct connection: (a,c) ∈ r. 
-/
inductive tc {α : Type} (r : α → α → Prop) : α → α → Prop
| base  : ∀ a b, r a b → tc a b
| trans : ∀ a b c, tc a b → tc b c → tc a c

/-
Here's a possibly surprising fact: the transitive 
closure concept *cannot be expressed, defined, nor the
concept used, in first-order predicate logic*. The
reason is that you can't quantify over relations, and
so cannot write "for any relation, r, it's transitive 
closure is ..." Quantifying over relations just isn't
allowed: it's not even part of the syntax of first-
order predicate logic.

Yet what we've written, formally and understandably, is
a concept essential in all kinds of logical reasoning in 
computer science. That suggests something about teaching
first-order logic as a first logic for computer science:
there's real reason to doubt that it's the best choice.
The higher-order predicate logic of Lean and similar
modern proof assistants is strictly more expressive.
-/

/-

-/

end relation
end relations

/-
Problem #1: Formally prove and give an English
language proof of the proposition that the identity
relation, on objects of an arbitrary type, β, is a
subrelation of any equivalence relation on β. 
-/

example : ∀ (β : Type) (r : β → β → Prop),
  equivalence r → subrelation relations.id_relation r := 
begin
  unfold equivalence subrelation reflexive relations.id_relation,
  assume β r h x y k,
  cases h with refl rest,
  rw <-k,
  exact refl x,
end

/-
Suppose r is a equivalence relation. To show that the
identity relation is a subrelation of r, we have to show
that for any pair, (x, y), in the identity relation, that
same pair is in r. Of course the identity relation has 
all and only the pairs of the form, (x, x), so all we 
need to show is that any such pair is also in r. But r
is reflexive, so by definition, for any x, (x, x) ∈ r. 
So (x,y) ∈ id_relation → (x, x) ∈ r. And that is what
it means for the identity relation to be a subrelation
of r. As r was arbitrary, the identity relation is a
subrelation of *any* equivalence relation on r. QED.
-/

/-
Prove that the ⊆ relation on sets of objects of any
type β is anti_symmetric (formally and informally).
-/

example : ∀ (β : Type), ⊆  

