
/--
From Sets to Relations

Take-away message. Whereas we represent a set
as a one-place predicate, we will represent a
binary relation as a two-place predicate. Just
as a set is a collection of individual objects
that satisfy a predicate, a relation is a set
of *pairs* of objects, each of which satisfies
the pair membership predicate for the relation. 
--/

/-
Example: negation_as_a_binary_relation on bool.
-/

def negation : bool → bool → Prop
| tt ff := true
| ff tt := true
| _ _ := false

/-
This predicate specifies the binary 
relation, {(tt, ff), (ff, tt)}. Each
member of the relation is an ordered
pair of Boolean values. The relation
comprises the set of all of the pairs 
that satisfy the predicate: make the
resulting proposition true. Other pairs 
of Booleans do not satisfy the predicate
and so are not in the relation that it
specifies. 
-/

/-

Note that unlike with the Boolean
negation function, bnot, we cannot
"compute" with predicates; we can
only try to prove that a pair of 
values (in this case) satisfy them.
-/

-- functions compute
#eval bnot tt
-- takes a single bool, returns a bool

example : negation tt ff := by unfold negation
-- takes two bools, returns a proposition
-- that proposition then has to be proved 
-- can use "by" when script is a single tactic

/-
Exercise: Formally state and prove the proposition
that for all Boolean values, b1 and b2, negation b1 
b2 ↔ bnot b1 = b2. This proposition claims that the
bnot function applied to a Boolean value, b1, equals
b2, if and only if the pair, (b1,b2), is "in" the
negation relation.   
-/

example: ∀ (b1 b2), negation b1 b2 ↔ bnot b1 = b2 :=
begin
assume b1 b2,
split,
-- What should be our proof strategy from here?
-- Exercise: complete this proof.
end 


/-
Next idea: A binary relation can relate objects of 
different types types. The last example was of a
binary relation relating bools to bools. Not let's
introduce a new data type, call it bit, with values
bit.zero and bit.one, and the consider a relation
"between" bools and bits, where a bool is either
tt or ff and a bit is either zero or one. 
-/

inductive bit : Type 
| zero : bit
| one : bit

/-
Here for fun is a function that takes a bit
and returns the other bit. It's like bnot but
for bits.
-/

def bit_flip : bit → bit 
| bit.zero := bit.one
| bit.one := bit.zero

/-
Now let's define a relation from bool to bit
that associates tt with one and ff with zero.
-/

def bool_to_bit_relation : bool → bit → Prop
| tt bit.one := true
| ff bit.zero := true
| _ _ := false

/-
Exercise: Draw a picture of this relation.
Exercise: Draw an adjacency matrix for this relation
-/

/-
As another concrete example, let's define the relation
between natural numbers and their squares. We'll start
by defining the square function. Then we'll define the
corresponding relation. They represent the same set of
ordered pairs, but the first computes and the second is
"declarative" (computational vs. logical).
-/

def square (n : ℕ) := n * n

/-
Now we specific the relevant set of pairs.
-/
def squares (n m : ℕ) : Prop := square n = m 

/-
We can prove pairs that bear this relationship and
not ones that don't.
-/

example : squares 0 0 := rfl
example : squares 0 0 := rfl
example : squares 1 1 := rfl
example : squares 2 3 := rfl    -- no can, dude
example : squares 2 4 := rfl
example : squares 25 625 := rfl


