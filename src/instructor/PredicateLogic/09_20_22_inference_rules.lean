/-

As a reminder, here are the inference rules (and a few
"logical fallacies" that you tested for validity in the
setting of propositional logic, where the variables are
all Boolean, and where logical connectives correspond to
Boolean operations, such as &&, ||, and ! (C, C++, etc.) 

1. X ∨ Y, X ⊢ ¬Y             -- affirming the disjunct
2. X, Y ⊢ X ∧ Y              -- and introduction
3. X ∧ Y ⊢ X                 -- and elimination left
4. X ∧ Y ⊢ Y                 -- and elimination right
5. ¬¬X ⊢ X                   -- negation elimination 
6. ¬(X ∧ ¬X)                 -- no contradiction
7. X ⊢ X ∨ Y                 -- or introduction left
8. Y ⊢ X ∨ Y                 -- or introduction right
9. X → Y, ¬X ⊢ ¬ Y           -- denying the antecedent
10. X → Y, Y → X ⊢ X ↔ Y      -- iff introduction
11. X ↔ Y ⊢ X → Y            -- iff elimination left
12. X ↔ Y ⊢ Y → X            -- iff elimination right
13. X ∨ Y, X → Z, Y → Z ⊢ Z  -- or elimination
14. X → Y, Y ⊢ X             -- affirming the conclusion
15. X → Y, X ⊢ Y             -- arrow elimination
16. X → Y, Y → Z ⊢ X → Z     -- transitivity of → 
17. X → Y ⊢ Y → X            -- converse
18. X → Y ⊢ ¬Y → ¬X          -- contrapositive
19. ¬(X ∨ Y) ↔ ¬X ∧ ¬Y       -- DeMorgan #1 (¬ distributes over ∨)
20. ¬(X ∧ Y) ↔ ¬X ∨ ¬Y       -- Demorgan #2 (¬ distributes over ∧)
-/


/-
Here we present the familiar inference rules above but 
now in the context of the more expressive, higher-order
predicate logic of the Lean Prover tool. A big benefit 
is that "Lean" checks the syntax of our expressions.

Note that we've reordered the inference rules you've already
seen, putting all of the inference rules related to any given
connective or quantifier together.

We've also added inference rules for the quantifiers, ∀ and
∃, which of course are not relevant in propositional logic 
but that are essential in predicate logic (whether first- or
higher-order).

We've also separate out, and present first, the fundamental
inference rules from "inference rules" that are can be proved
using the fundamental rules. These rules are thus "theorems,"
not "axioms." 
-/

/-
Ok. So each of the following lines does the following. As you
read this, look at the first definition, of and_introduction.

In Lean, we can use "def," a Lean keywork, to start to define
the meaning/value of a variable. After "def" comes the name of
the variable. Here it's and_introduction. Next comes what we
have already seen, albeit briefly: a type judgment, comprising
a colon followed by a type name. The type name in this case is
"Prop," which is the type of all *propositions* in Lean. So far
then we've told Lean that we're going to define and_introduction
to be a variable the value of which is a proposition. Next is 
a :=, which is the Lean operator for binding a value to a name.
Finally, the value to be bound is to the right. In this case,
as expected, it's a proposition. 

The particular proposition in this case is what we can call a 
"universal generalization" in that it starts with a ∀. The ∀ 
introduces two new variable names, X and Y, with a type judgment
stating that their values are propositions, indeed they can be
*any* propositions whatsoever. Finally, in the context of the
assumption that X and Y are arbitrary (any) proposition, the
rule states that if we assume that we are given a proof of X
(the analog of the assumption that X is true in propositional
or first-order predicate logic), and if in that context we then
further assume that we have a proof of Y (and thus that Y is 
also true), then in that context, we can construct a proof of
X ∧ Y, thus concluding that it, too, must be true.  
-/

-- ∧ 
def and_introduction  : Prop  := ∀ (X Y : Prop), X → Y → (X ∧ Y)
def and_elim_left     : Prop  := ∀ (X Y : Prop), X ∧ Y → X  
def and_elim_right    : Prop  := ∀ (X Y : Prop), X ∧ Y → Y  

/-
Note that we are able to express these rules of logic very
naturally in higher-order constructive logic because we can
quantify over propositions. You cannot write these definitions
in first-order logic because it doesn't allow you to do this.
Such an expression is a syntax error in first-order logic. 
-/

/- A LEAN DETAIL and IMPORTANT LANGUAGE DESIGN CONCEPT
A good language gives you good ways not to repeat yourself.
We can avoid having to repeatedly write "∀ (X Y : Prop),"
by creating a "section" in a Lean file, and declaring the
common variables once at the top. Lean then implicitly adds
a "∀ (X : Prop)" at the beginning of any expression that has
an X in it (and the same goes for Y and Z in this file).
I
-/

section pred_logic

variables X Y Z : Prop

/-
In your mind, be sure to recognize that every one of the
following propositions now has an implicit ∀ in front. The
or_intro_left definition that comes next, for example, means 
def or_intro_left : Prop := ∀ (X Y : Prop), X → X ∨ Y. 
-/

-- ∨ 
def or_intro_left : Prop    := X → X ∨ Y
def or_intro_right : Prop   := Y → X ∨ Y
def or_elim : Prop          := (X ∨ Y) → (X → Z) → (Y → Z) → Z

/-
Lean, and other languages like it, also allow you to drop
explicit type judgments when they can be inferred from the
context. In the rest of this file, we also drop the ": Prop"
explicit type judgments because Lean can figure our from the
values that follow the :='s that type types of the variables
here just have to be Prop.
-/

-- → and ∀ 
def arrow_all_intro   := ∀ (x : X), Y   ↔ X → Y
def arrow_elim        :=  (X → Y) → X       → Y
def all_elim          := ((∀ x : X), Y) → X → Y

-- ↔ 
def iff_intro         := (X → Y) → (Y → X) → X ↔ Y
def iff_elim_left     := X ↔ Y → (X → Y)
def iff_elim_right    := X ↔ Y → (Y → X)

/-
The inference rules for and, or, implies, forall, and
biimplication are "not to bad." The rules for negation
and exists are a little trickier: not terrible but they
do require slightly deeper understanding. 
-/


-- ¬ 
def not_ (X : Prop) := X → false  -- this is how "not" ¬ is defined in CL
def excluded_middle   := X ∨ ¬X   -- not an axiom in constructive logic
def neg_elim          := ¬¬X → X  -- depends on adoption of em as an axiom

/-
Now we get to exists. And for this explanation, we need to first nail
down the concept of a predicate in predicate logic. As we've exaplained
before, a predicate is a proposition with one or more parameters. Think
of parameters as simply blanks in the reading of the proposition that 
you can fill in with any value of the type of value that is permitted
in that slot. When you fill in all the blanks (by giving actual values
for the formal parameters). you finally get a proposition: a specific
statement about specific objects with no remaining blanks to be filled
in. Whereas a predicate gives rise to a family of propositions, once 
all the parameters are bound to actual values, you've no longer got a
predicate. 

As a test of your understanding of what was just said, does it make
sense to you that if you have a predicate with zero parameters, that's 
a proposition? How about this: if you've got a predicate with, say, 
found arguments/parameters, and you fix the value of one of these
parameters to a specific actual value of the right type, the result
is a still predicate, but now with one less, now three remaining
parameters? That is true. 

The way we represent a predicate with one argument of some type, T,
is as an object, a predicate, P, of type T → Prop. KEY IDEA: Look 
back at → elimination. It says that if you have a "proof object" 
of T → Prop, and you have an object, t, of type T, then you can
derive something of type Prop: a proposition! In other words, you
can *use* a predicate, P : T → Prop if you also happen have or if
you can acquire an object (t : T). 

MAKE SURE YOU SEE THIS POINT. IF YOU DON'T FIND PEOPLE WITH WHOM
YOU CAN TALK IT THROUGH. GO ON PIAZZA IS GOOD ADVICE.

Ok, so from now on, when you see anything that looks like T → Prop,
you think, "Ok, that's just a predicate, a proposition with a blank,
where the blank can be filled in by any object of type T, whatever
that type might be." This formulation works for all types. Example:
Suppose T is Person. Then (isNice : T → Prop) is a predicate that
takes a person, let's call them p, as an argument, and "reduces to"
the proposition, (isNice p). In English we'd just say, "p is nice."

Finally, a crucial point: we can represent *properties* of things
as predicates. A property of an object is a characteristic that it
as an individual possesses. As an example, think of the universe 
of all balls used in sports: all those individual balls. Now think
of a property that some of those balls have: in particular consider
the property of being blue. Some balls have this property, some
doon't. Or in the realm of intengers, some have the peropty of
being even, or prime, or beautiful, and some don't. 

Let's take a property over the integers, specifically the property
of being even. We will represent this property as a predicate, call
it isEven : ℤ → Prop. (ℤ is the symbol most mathenaticians use to
represent the integers.) isEven is thus some property of natural
numbers in the following sense: given any integer, n, (isEven n) is
a *proposition* that we interpret as asserting that n is even. To
be concrete, (isEven 3) we interpret as the proposition that three
is even. Under our ordinary definitions of these terms,, it's false,
but still a perfectly good proposition. On the other hand, isEven 4,
we be a proposition one for which we can construct a proof. The set
of all numbers *for which its proposition is true* is the set of 
objects that we say "has the property" that the predicate "tests
for." A property in a sense is a specific subject of objects of a
given type, namely all those that *satisfy* the constraint that
the predicate defines: of being even, prime, beautiful, or whaever.
-/



-- ∃
def exists_intro := ∀ {P : X → Prop} (w : X), P w → (∃ (x : X), P x) 
def exists_elim := ∀ {P : X → Prop}, (∃ (x : X), P x) → (∀ (x : X), P x → Y) → Y 


/-
That's it for the fundamental rules of higher-order predicate
logic. The constructive logic versions of the remaining inference
rules we saw in propositional logic are actually theorems, which
means that they can be proved using only the fundamental rules,
which we accept as axioms. An axiom is a proposition accepted as
true without a proof. The inference rules of a logic are accepted
as axioms. The truth of any other proposition in predicate logic
(the foundation for most of mathematics) is proved by applying 
fundamental axioms and previously proved theorems..  
-/

-- theorems
def arrow_trans       := (X → Y) → (Y → Z) → (X → Z)
def contrapostitive   := (X → Y) → (¬Y → ¬X)
def demorgan1         := ¬(X ∨ Y) ↔ ¬X ∧ ¬Y
def demorgan2         := ¬(X ∧ Y) ↔ ¬X ∨ ¬Y
def no_contradiction  := ¬(X ∧ ¬X)


/-
Here are the logical fallacies we first met in propositional
logic, now presented in the much richer context of constructive
logic. You might guess that it will be impossible to construct
proofs of these fallacies, and you would be correct, as we will
see going forward.
-/
-- fallacies
def converse          := (X → Y) → (Y → X)
def deny_antecedent   := (X → Y) → ¬X →  ¬Y
def affirm_conclusion := (X → Y) → (Y → X)
def affirm_disjunct   := X ∨ Y → (X → ¬Y)

end pred_logic