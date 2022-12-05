import data.set

/- #1

Prove that if there's an object, a, of some type, α, 
having some property (satisfying a predicate), P, then 
not every object of type α fails to have property, P.
-/

example (α : Type) (P : α → Prop) : (∃ a, P a) → (¬(∀ x, ¬ P x)) :=
begin
assume h,
cases h with w pw,
assume k,
have npw := k w,
contradiction,
end

/- Extra credit. 

The converse of this proposition is clasically true. If
not every object has propery, P, then there must be some
object that has it. If you try to prove the converse in
our constructive logic, what happens? Show you work, and
then briefly but clearly explain exactly what goes wrong.
-/

/- #2

Consider the following binary relation, r, with domain
and the co-domain both being ℕ.

( domain = ℕ, r = {(0,0),(1,1),(2,2)}, co-domain=ℕ )

A. Is this relation reflexive? Explain your answer.

No. Not *every* object of the domain is related to itself.

B. Is this relation symmetric? Explain your answer.

Yes, the reverse of every pair in the relation is also
in the relation. 

C. Is this relation transitive? Explain your answer.

Yes. In all cases (there are none!) in which an a is
related to a b, and a b is related to a c that a is 
related to that c. Again there are *no* such cases, so,
again, the it's true for all of them!

D. Is this relation an equivalence relation? Explain.

No. It's not reflexive.

-/

/- #3

A binary relation, r, is said to be *anti-symetric* 
if, for all values in its domain, a and b, if r a b 
and if r b a then a = b. Give an example of a familiar
arithmetic relation that's anti-symmetric, and briefly
explain why it's so.

Answer: less than or equals is an anti-symmetric 
relation. If a <= b and b <= a then it must be that
case that a = b.
-/


/- #4
A binary relation, r, is said to be asymmetric if
whenever, for any a and b, if r a b then ¬ r b a. 
-/

/- A.

First, express this idea formally by completing the 
following definition.
-/

def is_asymmetric 
  {α : Type} 
  (r : α → α → Prop) : 
  Prop 
  := 
∀ (a b : α), r a b → ¬ r b a 

/- B.

Name a familar arithmetic relation that's asymmetric
and briefly explain why you think it's asymmetric.

Answer here: The less than relation (on natural numbers)
is asymmetric because for any a, b, if a < b then ¬ b < a.

-/

/- C: 

An object cannot be related to itself in an asymmetric
relation. First, complete the following informal proof
of this statement.

Proof: Assume α, r, and a are as given (and in particular
assume that r is asymmetric). Now assume r a a. 

Answer here (rest of proof): From the fact that r is
asymmetric and given the assumption that r a a, we can 
conclude ¬ r a a. That's is a contradiction. The r a a
cannot have been true. Since a was arbitrary, no a can
be related to itself.
-/

/- D.

Now prove a closely related proposition formally. 
Add a comment to each line of your formal proof 
so as to construct a good skeleton for a fluent 
English language proof.
-/

example
  (α : Type) 
  (r : α → α → Prop)
  (h : is_asymmetric r) :
¬ ∃ (a : α), r a a :=
begin
-- proof by negation
-- suppose there is such an a
assume h,
-- let's call it w with a proof of r w w 
cases h with w pf,
-- apply generalization h to w and w to deduce h w w 
let contra := h w w,
-- apply resulting implication to proof of r w w
let contra2 := contra pf,
-- that gives a proof of ¬ r w w
-- and that is a ...
contradiction,
-- So the assumption there is such an a is false
-- QED.
end

/- #5
Prove that equality on an inhabited (non-empty) type 
is not assymetric.
-/

example (α : Type) (a : α): ¬ is_asymmetric (@eq α) :=
begin
-- assume equality is asymmetric
assume h,

-- expand definition
unfold is_asymmetric at h,

-- apply h to derive a proof of 
-- of a = b → a ≠ b
let x := h a a,

-- apply it to a proof of a = a
let y := x (eq.refl a),

-- now we have a contradiction
contradiction,

-- so equality must not be asymmetric
-- if α is an inhabited (non-empty) type
-- which the argument, a, assures is so
end

/- #6
Two natural numbers, p and q, are said to be 
"equivalent mod m" if p % m = q % m, which makes
"equivalence mod m" a binary relation on natural
numbers. Here's a formal definition of this binary
relation on the natural numbers (given an m).
-/

def equiv_mod_m (m : ℕ) : ℕ → ℕ → Prop := 
  -- given m, equiv_mod_m is a binary predicate
  λ p q : ℕ, p % m = q % m

/-
Prove using Lean's definitions "equivalence" that 
equiv_mod_m is an equivalence relation for any natural
number, m. Here you'll use Lean's definitions of
equivalence, reflexive, symmetric, and transitive. 
-/

example : ∀ m : ℕ, equivalence (equiv_mod_m m) :=
begin
-- assume arbitrary "modulus"
intro m,

-- expand definition
unfold equivalence,

-- split goal into three conjuncts
apply (and.intro _ (and.intro _ _)),

-- prove reflexivity
unfold reflexive,
assume x,
unfold equiv_mod_m,

-- prove symmetry 
unfold symmetric,
assume x y h,
unfold equiv_mod_m at h,
unfold equiv_mod_m,
rw h,

-- prove transitivity 
unfold transitive,
assume a b c,
assume h k,
unfold equiv_mod_m at h,
unfold equiv_mod_m at k,
unfold equiv_mod_m,
rw h,
rw k,
-- That suffices to prove the theorem!
end

/- #7
Consider the relation, tin_rel, that associates people 
with U.S. taxpayer id numbers, which we'll represent as 
natural numbers here. 

Assume this relation is single-valued. Which of the 
following properties does this relation have? Give
a very brief justification of each answer. Assume
the domain is all living persons, and the co-domain
is all natural numbers.

-- it's a function: Yes, person has (should have) more than one ssn/tin
-- it's total: No, not every person has an ssn/tin
-- it's injective: yes, no two people can have the same ssn/tin 
-- it's surjective (where the co-domain is all ℕ): no, not every ℕ is an ssn
-- it's strictly partial: yes, there are people without ssns
-- it's bijective: no, it's not surjective
-/


/- #8
Suppose r is the empty relation on the natural 
numbers. Which of the following properties does
it have? Explain each answer enough to show you
know why your answer is correct.

-- reflexive: no, because not every number is related to itself in r
-- symmetric: yes, because it's a generalization over an empty set
-- transitive: yes, because its a generalization over an empty set
-/


/- #9
Here's a formal definition of this empty relation.
That there are no constructors means there are no 
proofs, which is to say that no pair can be proved
to be in this relation, so it must be empty.
-/

inductive empty_rel : ℕ → ℕ → Prop

/-
Formally state and prove you answer for each of the
three properties. That is, for each property assert
that either empty_rel does or does not have it, then
prove your assertion. Include English-language comments
on each line to give the essential elements of a good
English language proof.
-/


example : ¬reflexive empty_rel :=
begin
unfold reflexive,
assume h,
let x := h 0,
cases x,
end

example : symmetric empty_rel :=
begin
unfold symmetric,
assume a b h,
cases h,
end

example : transitive empty_rel :=
begin
assume a b c h k,
cases h,
end

/- #10
A relation, r, is said to have the property of being 
a *partial order* if it's reflexive, anti-symmetric,
and transitive. Give a brief English language proof 
that the subset relation on the subsets of any set, 
S (of objects of some type), is a partial order. 

Pf:  
Suppose S is a set, with a ⊆ S and b ⊆ S subsets. Then

1. every such a is a subset of itself, so reflexive
2. if a ⊆ b and b ⊆ a then a = b, so anti-symmetric
3. if a ⊆ b and b ⊆ c, then a ⊆ c, so transitive
    given x ∈ a, a ⊆ b means x ∈ b, and similarly 
    because x ∈ b then x ∈ c, so x ∈ a → x ∈ c,
    which is the definition of a ⊆ c. QED.
-/

/- #11 
Finally we return again to DeMorgan's laws, but
now for sets. You'll recall that these "laws" as we
have seent them so far tell us how to distribute ¬  
over ∨ and over ∧. You will also recall that set
intersection (∩) is defined by the conjunction (∧) 
of the membership predicates, set union (∪) by the
disjunction (∨), and set complement (Sᶜ for a set,
S), by negation (¬). It makes sense to hypothesize 
that we can recast DeMorgan's laws in terms of the
distribution of complement over set union and set
intersection. Indeed we can. Your job is to state
and prove (formally) the first DeMorgan laws for 
sets, which states that the complement of a union
of any two sets equals the intersection of their 
complements.

Hint: To prove that two sets are equal, S = T, use
the ext tactic. It applies an axiom that states it
suffices to prove S ↔ T, viewing the sets as being
defined by their logical membership predicates. You
know how to handle bi-implications. The rest you 
can do by seeing "not," "and," and "or" in place 
of complement, conjunction, and disjuction, resp.  
-/

example 
  (α : Type) 
  (a b: set α) :
(a ∪ b)ᶜ = aᶜ ∩ bᶜ := 
begin
-- To prove two sets equal we can show their membership predicates are equivalent
ext,  

-- Prove implications in both directions
split,

-- forwards

-- assume premise
assume h,

-- eliminate ∧/∩ in h
-- h says x ∈ a ∨ x ∈ b → false
-- show x ∈ aᶜ and x ∈ bᶜ 

apply and.intro,
assume k,
let foo: (x ∈ a ∪ b) := 
  begin left, assumption end,
contradiction, 

assume k,
let foo: (x ∈ a ∪ b) := 
  begin right, assumption end,
contradiction,

-- backwards
assume h,
assume k,
cases k,
cases h,
contradiction,
cases h,
contradiction,
end

/-
Post-HW exercise: Write a fluent English language proof
of the preceding proposition. Hint: Model it on the formal
proof.
-/
