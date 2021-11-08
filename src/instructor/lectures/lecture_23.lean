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
Additional properties of relations
-/

def strongly_connected := ∀ x y, x ≺ y ∨ y ≺ x
def total := @strongly_connected β 
/-
Note: we will use "total" later to refer to a different
property of relations that also satisfy the constraints
needed to be "functions."  To avoid ambiguity we will
prefer the term, "strongly_connected," over "total."
-/

def anti_reflexive := ∀ x, ¬ x ≺ x
def irreflexive := anti_reflexive r -- sometimes used
def anti_symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x

/-
CLOSURE operations on relations.

Given a relation, r, the reflexive, symmetric, or
transitive closure of r is the smallest relation that
(1) contains r, and (2) contains any additional pairs
needed to make the resulting relation reflexive, or
symmetric, or transitive, respectively. The reflexive,
symmetric, transitive closure of r is the smallest
relation (which means *no* unnecessary added pairs)
that contains r and has all three properties. Note
that the resulting relation will be an equivalence
relation. The meaning of this is basically that if
anything is connecting to somethiing else, they will
end up in the same "equivalence class." We'll see a
picture.
-/

def reflexive_closure := λ (a b : β), (r a b) ∨ (a = b)
def symmetric_closure := λ (a b : β), (r a b) ∨ (r b a)

/-
Let's look examples. What's in the reflexive closure
of { (0,1), (1,2), (2, 3), (3, 4), (4, 5) }? It is 
often easier to think about these things with the aid
of a picture, so let's draw this relation and see in
graphical terms what it means to compute its reflexive
closure.
-/

/- 
The definitions of the reflexive and symmetric closures
of a relation are pretty easy to state. It's a little 
harder to say what set of pairs is in the transitive
closure of a given relation, r. Clearly it's a relation, 
r', where r' is the smallest relation that contains r 
and that is transitive. In other words, (tc r) is r
with any additional pairs needed to make the result
transitive.

What set of pairs is this? Well, (1) it contains every
pair in r, and (2) if (a,b) is in (tc r) and if (b, c)
is in (tc r), then (a, c) must also be in r. The way we
will say this formally uses what we call an inductive
definition. Inductive definitions allow for "bigger"
things to be built whenever there are smaller things
of the right kind.

Consider this relation, r = { (0,1), (1,2), (2, 3) }.
It's transitive closure clearly contains all three of
these pairs. What else must it include at a minimum to
be transitive?

Consider r = { (0,1), (1,2), (2, 3), (3, 4), (4, 5) }.
What is its transitive closure?

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
end relation
end relations

