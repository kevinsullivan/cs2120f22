# Predicate Logic and Relations through Equality

Equality is defined for all objects of all types
by just two inference rules, which we accept as
axioms. 

- the axiom of the *reflexivity of equality*
- the axiom of the *substitutability of equals*

We've seen the first (the reflexivity of equality).
In today's class, we'll quickly review the first,
then we'll introduce the second axiom. The comes
the real eye-opener: we will use these two axioms
to construct proofs of two theorems about equality:

- theorem: the equality relation is *symmetric*
- theorem: the equality relation is *transitive*

## Properties of relations

Speaking informally, when we say that a relation,
such as equality, is *symmetric* we're mean that,
for all objects, x and y, of any type T, if x is
related to y, then y is symmetrically related to x.

If the relation in question is equality, then what
it means for equality to be symmetric is that *if*
x = y (for *any* x and y of any type), then y = x.

By transitive, we mean that if x is related to y
and y is related to z, then x is related to z.

Example: Consider the friends relation on people
in Facebook. Is it reflexive? symmetric? transitive?

Example: Consider the "has a crush on" relation
on people. Is it reflexive? symmetric? Transitive?

Example: Consider the less than relation on
natural numbers. Is it symmetric? Transitive?

Example: Consider the less than or equal relation
on natural numbers. Is it Symmetric? Transitive?

## The reflexivity of equality is an axiom

You've already learned the reflexivity axiom
for equality: ∀ (T : Type) (t : T), t = t.

A direct translation could be, "Given any
type, T, and any object, t, of that type,
t is equal to itself." Put more succinctly,
"Every thing is equal to itself." But best
of all, "Equality is a *reflexive* relation."

## Propositions and predicates

These concepts are fundamental in all logics.

### Propositions

A proposition is a claim that can be judged
to be true or not. In mathemtical logic, a
proposition can be judged to be true if and
only if it is either an axiom, or a proof of
it can be derived by application of inference
rules to axioms.

Example: 3 = 4

- Truth value: false
- Proof: a false proposition has no proofs (else it'd be true!)

Example: 3 = 3

- Truth value: true
- Proof:
  - Informal: By the reflexivity of equality (for natural numbers)
  - Formal (in Lean): *eq.refl 3*
- Note: Each type (e.g., nat) has its own equality relation

Example: CVille is a city in Virginia

- Truth value: true
- Proof (evidence): city, county, state codes

Example: Kevin Sullivan is from Charlottesville

- Truth value: false
- Proof: none

### Predicates

A predicate is a parameterized proposition. In other words,
it is a proposition with some *arguments*, which is to say,
slots where you can fill in values of specified types.

Examples:

- predicate P: _X_ is a city in Virginia
  - fill in a value for _X_ to get a proposition
  - the resulting proposition could be true or not
  - if true of some _X_, _X_ "has the property of being a city in VA"
- predicate Q: _X_ is from Charlottesville
- predicate eq3: _X_ = 3
  - fill in a value (here a natural number) for _X_ to get a proposition
  - if true, then _X_ "has the property of being equal to 3"
  - of course there is a number, 3, that *satisfies* this predicate

Suppose that for predicates P and Q, the type of 
_X_ is string. You can then *apply* either predicate,
P or Q, to a string to get a resulting proposition.

For example, (Q "Kevin") produces the proposition,
Kevin Sullivan is from Charlottesville, while (e3 2)
produces the proposition 2 = 3.  

You can think of a predicate as a function: one that
takes values of given types as arguments and that returns
a *proposition* with the argument values plugged in where
the predicate had its formal parameters. A predicate really
is like a function that returns a proposition: it takes one
or more values as arguments, and returns a proposition that
makes an assertion *about* those values, as a result.

### Predicates as functions

Speaking formally, we represent a predicate exactly as a
function. In the case of the predicate e3, it's a function
that takes a natural number, n, and returns the proposition,
n = 3. Here's what this function looks like in Lean.

def e3 (n : nat) : Prop := n = 3

Applying e3 to 2, for example, yields the proposition,
2 = 3. This proposition is "about 2" in the sense that
it claims (falsely) that 2 has the property of being equal
to 3. The proposition has no proofs given that the only proofs
of equality we can construct are proofs that a value is
equal to itself. Implicit in this informal argument is the
assumption that 2 and 3 are different objects (which they
are, but that requires a discussion of the axioms that
define the natural numbers, which we'll skip for now).
So we can conclude that 2 does not have the property of
being equal to 3, and the proposition, (e3 2), i.e.,
2 = 3, is false.

## Constructing proofs of equality (introduction rule)

You've already learned the reflexivity axiom
for equality: ∀ (T : Type) (t : T), t = t.

A direct translation could be, "Given any
type, T, and any object, t, of that type,
t is equal to itself." Put more succinctly,
"Every thing is equal to itself." But best
of all, "Equality is a *reflexive* relation."

## Using proofs of equality (elimination rule)

We now turn to the second of the two axioms that
define equality: the axiom of the *substitutability
of equals*. This axioms is not used to create proofs
of equality but gives us a way to *use* a proof of
an equality in the construction of a different kind
of proof: to deduce, for any predicate, P, that if
(P x) is true, and x = y  is true, then (P y) must
also be true.

Example. If "Kevin is from Cville" and Kevin = Bob,
then we can deduce that "Bob is from Cville."

Example: If we know that (x + 2) = 7, and we also
know that "x = y," then we can conclude that y + 2
= 7.

In other words, the second axiom gives us a license
to *rewrite* propositions by replacing one term with
another as long as we can prove a proof of equality
as an argument. 

Here's the idea presented in the formal language
of predicate logic.

``` lean
axiom eq_subst :    -- arguments are assumptions!
  ∀ (T : Type)      -- if we're given, T, a type
    (P : T → Prop)  -- P, property of T objects (predicate)
    (x y : T)       -- x and y, objects of type T,
    (e : x = y)     -- e, a proof of x = y (we *use* an = proof)
    (px : P x),     -- a proof that x has property P
  P y               -- then we can have a proof of P y
```

Given any type, T, and any *property*, P, of objects
of this type (P : T \to Prop), if you know (x : T)
has property P (written as P x) and you know that
x = y, then you can deduce P y: y has property P.

### Example using substitutability axiom

In the context of the following assumptions ...

``` lean
axioms
  (T : Type)
  (P : T → Prop)
  (x y : T)
  (e : x = y)
  (px : P x)
```

Can we prove P y?

English: We've assumed that P x is true, and x = y,
so P y must be true by the substitutability of equals.

Formal:

``` lean
example : P y := eq_subst T P x y e px
```

So that's it as far as the axioms of equality
are concerned. Now we come to the remarkable
fact that from these two axioms, it can be
proved that the equality relation has two
additional crucial properties.

### Theorem: Equality is symmetric

Theorem: equality is symmetric.

Proof. Assume T is some type and x and
y are objects of this type. To prove that
equality is symmetric, we must prove that,
for *any* x and y of this type, if x = y
then it must be the case that y = x.

By the axiom of the substitutivity of
equals, y = x is equivalent to y = y
(rewriting the x as y justified by the
assumption that x = y); but y = y is
true by the axiom of the reflexivity
of equality, and so the proof is done.
QED.

Here's a less verbose proof.

Proof: By the substitutability of equals,
we can rewrite y = x as y = y, but this is
true by the reflexivity of equality. QED.

Here's another way.

1. T is a type               assumption
2. x and y are of type T     assumption
3. x = y                     assumption
4. y = x                     goal
5. y = y                     by substitutability using 3
6. QED                       by reflexivity

### Theorem: Equality is transitive

If x, y, and z are objects of some type, T, and we
know (have proofs or axioms) that x = y and y = z,
then we must show (construct a proof) that x = z.

The argument is very similar to that for symmetry.

Proof. We are given as assumptions that T is a
type; x, y, and z are values of this type; and
that x = y and y = z. In this context, we are to
show that x = z. We first apply substitutability
using our proof of x = y to rewrite the x in the
goal to y, yielding a new goal: y = z. But that
is something we've already assumed is true. QED.

## Conclusion

What you have now seen is the essence of a logical
argument (proof). We start with given axioms (such
as the reflexivity and substitutability of equals),
and from them we then deduce (construct proofs of)
new facts (such as the symmetry and transitivity 
of equality). This is how all of mathematics works!
