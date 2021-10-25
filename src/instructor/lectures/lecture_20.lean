import data.set
/-
The preceding import statement imports 
definitions for set theory beyond those
that are included in the libraries that
are loaded by default when Lean starts.
-/

/-
We've now seen how sets correspond in
very close ways) to one-place predicates.
This correspondence allows us to "reduce"
the language of set theory to the language
of predicate logic (here, in Lean). That,
in turn, let's use predicate logic and our
proof building and checking machinery to  
write propositions *in set theory* and to
develop and automatically check proofs.
-/

/-
We will continue in this vein as we now
consider a powerful generalization. If a
one-place predicate can represent a set
of individual values, a two-place predicate
can represent a set of pairs of values. A
three-place predicate can represent a set
of 3-tuples of values. Etc. We call such
sets *relations*. 

Here's an example: consider the set of 
pairs of natural numbers, where in each
pair the second number is exactly one more
than the first number, and where the first
numbers are 0, 1, and 2. The set of pairs 
that satisfies this specifications is 
{ (0, 1), (1, 2), (2, 3) }.

Here's another example. Suppose α is
string and β is nat. We can specify a
*relation* between strings and natural
numbers, where a pair, p = (s, n), is
in the relation if an only if n is the
length of s (in that specific pair).  

Here are some "tuples" (pairs in this
case) that would be "in" this relation:
("Yo",2), ("Lean",4), ("Rocks!",6). A
pair that is excluded is ("Naw!",5), as
5 is not equal to the length of "Naw!".

We haven't give an algorithm here to
*compute* the elements of this relation, 
but we have precisely *specified* what
it is (as long as we properly define
nat, string, length; we'll get there).
-/

/-
The idea that you should now have in mind
is that we can represent a "binary relation
on α ⨯ β", which mathematically is a set of
α-β pairs, as a two-place predicate. We can
then *verify* that any given pair is in the
relation (if it is) by producing a proof of
that fact.
-/

/- EXAMPLE: equality

To further ground the discussion, let's
return to the equality relation. For any
type, α, we have an equality relation. If
α is ℕ, for example, then we have equality
defined on the natural numbers. Some pairs
that would be "in" the relation are in the
set: {(0, 0), (1, 1), ..., (n,n), ...}.
Pairs that would not be in the relation
include (1, 2), (3, 9), and so forth.
-/

#check @eq nat
#check @eq string
#check @eq bool

/-
The way we assure these properties is by 
defining new introduction axioms for a
given relation in such a way that they
can construct all and only the proofs 
that should be true. For example, eq.refl
takes a single argument, e.g., n, and in
return produces a proof of n = n. That's
all the introduction rules for eq, and so
anything can be proved equal to itself and
no other equality proposition are provable.

We haven't seen how to define predicates
with associated proof construction rules,
yet, but we will when we see how to define
our own types (propositions are types and
predicates are thus types with parameters).
Suffice it to say for now that different
relations will have different introduction
rules!
-/

/-
Let's now visualize the set of all pairs 
of type ℕ ⨯ ℕ. Again, ℕ ⨯ ℕ is a type. It
is the type of *pairs*, such as (p.1, p.2),
where each of p.1 and p.2 are of type ℕ. 

Just think of a 2-D table, with natural 
numbers going up from zero across the top 
and the same down the left side. The pairs
correspond to the cells where the rows and
columns intersect in the table. Eventually
every possible pair appears in the table. 

A relation is a *subset* of all such pairs,
namely all and only those pairs that satisfy
the membership predicate for the relation:
just as with sets! In mathematical writing
we will therefore often see definitions 
like this:

Let R ⊆ ℕ × ℕ be a binary relation such 
that ∀ (n m ∈ ℕ), (m, n) ∈ R ↔ n = m + 1.
Note that we're using "ordered pair notation"
to represent pairs, i.e., values in ℕ × ℕ 
in this case. Lean supports these standard
notations.  
-/

-- Here's a product type
#check ℕ × ℕ 

-- Here's a value of this type
#check (1, 1)


/-
And here are some relations. Take a minute
to read and understand exactly what pairs 
are in each of these sets, and express your
answers in English.
-/
#check { p : ℕ × ℕ | p.1 <= p.2 }
#check { p : ℕ × ℕ | p.2 = p.1 * p.1 }
#check { p : string × ℕ | p.2 = string.length p.1}


/-
What we've now got again is a "reduction"
from the mathematical concept of sets to
predicate logic. We can then use logic to
*verify* that a particular pair is or is 
not in a particular relation using all of
our usual theorem proving tools!
-/

example : (1, 1) ∈ { p : ℕ × ℕ | p.1 <= p.2 } :=
begin
  show { p : ℕ × ℕ | p.1 <= p.2 } (1, 1), -- apply predicate
  show 1 <= 1,                            -- proposition
  exact nat.less_than_or_equal.refl,      -- proof
end

/-
In English, the proposition is true by the
reflexive property of ≤. 
-/

example : (3, 9) ∈ { p : ℕ × ℕ | p.2 = p.1 * p.1 } :=
begin
  show 9 = 3 * 3,
  exact rfl,
end

/-
In English, the proposition is true by the reflexive
property of =.
-/

example : ("Hello", 5) ∈ { p : string × ℕ | p.2 = string.length p.1} :=
begin
  exact rfl,
end

-- Proof by reflexivity of =.

example : (3, 10) ∈ { p : ℕ × ℕ | p.2 = p.1 * p.1 } :=
begin
  show 10 = 3 * 3,
  exact rfl, -- stuck
end

-- stuck (in fact it's provably false)

example : (3, 10) ∈ compl { p : ℕ × ℕ | p.2 = p.1 * p.1 } :=
begin
  show ¬10=9,
  assume h,
  cases h,
end

-- Proof by negation and the reflexive property of =.

/-
Now please do this: take out a piece of paper and 
a pencil or pen draw the first 4 or 5 rows and
columns to make a grid, and now put a little check 
mark in each cell in the grid that satisfies the 
specification: that the first nunber in the pair 
(let's let that be the row number) is less than or 
equal to the second, (the column number). 

Each cell corresponds to a proposition, and you
have just marked exacty the ones for which you 
want to have proofs. The definition of the intro
rule for <= precisely assures that this is so.
In Lean the relation is le. Look at the type
of nat.le. It's ℕ → ℕ → Prop. It's a two-place
predicate, but the key point here is that it's
defined to express exactly the "less than or
equal to  
-/

#check nat.le

/-
At this point you might be wondering where do
the introduction rules to build proofs to show
that certain values satisfy a given predicate. 

The answer is still a little bit beyond what
we're fully equipped to handle right now, but
the general idea can now be stated.

A predicate is a type of function that takes
some arguments and yields some propositions, 
one for each possible combination or arguemnt
values. The question is, where are the rules
defined determine how to construct proofs for
and such proposition. 

The technical answer is that they are given
by "proof constructor" (axioms) defined right
along with the predicate, itself. Here for 
example is the type definition of the ≤
relation in Lean. (Just real Π as being ∀.)
The first rule says you can prove a ≤ a for
any a, and the second rule says that if you
know that a ≤ b, for any a and b, that you
can then also prove a ≤ (b + 1). That's it.

inductive less_than_or_equal (a : ℕ) : ℕ → Prop
| refl : less_than_or_equal a
| step : Π {b}, 
    less_than_or_equal b → 
    less_than_or_equal (succ b)

(Note that in the definition, the predicate
takes two arguments, first a, and then some
value of type ℕ as required by ℕ → Prop). It
is easiest and just fine for now to think of
it as just taking two parameters and giving
a proposition, for which the proof rules are
given by the constructors!
-/

#print nat.le

/-
Here are proofs of 0 ≤ 0, 0 ≤ 1, and
0 ≤ 2.
-/
example : 0 ≤ 0 :=    -- nat.le 0 0
begin
  exact nat.less_than_or_equal.refl,
end

example : nat.le 0 1 := 
begin
  apply nat.less_than_or_equal.step,
  exact nat.less_than_or_equal.refl,
end

example : nat.le 0 2 := 
begin
  apply nat.less_than_or_equal.step,
  apply nat.less_than_or_equal.step,
  exact nat.less_than_or_equal.refl,
end

/-
How about proving 0 ≤ 2 in English.
"To prove 0 ≤ 2, by the step rule, it
will suffice to prove 0 ≤ 1. To prove
0 ≤ 1, it will suffice to prove 0 ≤ 0.
And a proof of this is given by the
reflexivity of ≤. QED."
-/

/-
Now think about these two questions: 
(1) which entries in a table of ℕ × ℕ 
are "filled in" by the refl rule? And
which by the step rule? Can you see how 
the step rule fills in *all* cells to
the right of the diagonal, "inductively" 
(one step after another for any finite
number of times)? 
-/
