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

To understand what those theorems are saying before
we get into how we can prove them using our axioms,
we must cover the *properties of relations* called
symmetry and transitivity.

### Symmetry

Speaking informally, when we say that a relation,
R, such as equality, is *symmetric* we're mean that,
for *any* objects, x and y, if R relates x to y,
then R also relates y to x.

If the relation in question is equality, then what
it means for equality to be symmetric is that *if*
x = y (for *any* x and y), then it must also be
that y = x. (Otherwise R would not be symmetric.)

### Transitivity

When we say that a relation r, is transitive, we
mean that, for all objects, x, y, and z, if x is
related to y by r, and y is is related to z by r,
then x must be related to z by r (otherwise r is
not transitive).

Example: Consider the friends relation on people
in Facebook. Is it reflexive? symmetric? transitive?

Example: Consider the "has a crush on" relation
on people. Is it reflexive? symmetric? Transitive?

Example: Consider the less than relation on
natural numbers. Is it symmetric? Transitive?

Example: Consider the less than or equal relation
on natural numbers. Is it Symmetric? Transitive?

## Propositions and predicates

Next it's important to understand what we mean
by the terms, and how we use, propositions and
predicates. These concepts are fundamental in
all logics.

### Propositions

A proposition is a "claim," an *assertion* that
some state of affairs holds. A proposition can
be *judged* to be true or false. In mathematical
logic, a conjecture--a proposition for which one
does not yet have a proof---asserts that some
mathematical formula is valid.

If one can produce a proof of the conjecture then
one can render the judgement that that proposition
is true. A proof of it establishes it as a theorem.
And from that point on, the theorem can be applied
as if it were just another axiom, in constructing
proofs of ever more elaborate conjectures.

Example: 3 = 4

- Truth value: false
- Proof: a false proposition has no proofs (else it'd be true!)

Example: 3 = 3

- Truth value: true
- Proof:
  - Informal: By the reflexivity of equality (for natural numbers)
  - Formal (in Lean): *eq.refl 3*
- Note: Each type (e.g., nat) has its own separate equality relation

Example: Kevin Sullivan (your professor) is from Charlottesville

- Truth value: false
- Proof: none

### Predicates

A predicate is a parameterized proposition: a proposition with
*arguments* (just like a function has arguments). When you fill
in all of the arguments of a predicate, you have a proposition,
just like when you fill in all the arguments to a function call,
you get a result.

Examples:

- predicate P: _X_ is a city in Virginia
  - fill in a value for _X_ to get a proposition
  - the resulting proposition could be true or not
  - if true of some _X_, we say that _X_ *has the property of* being a city in VA
- predicate Q: _X_ is from Charlottesville
- predicate eq3: _X_ = 3
  - fill in a value (here a natural number) for _X_ to get a proposition
  - if true, then _X_ "has the property of being equal to 3"
  - the number, 3, *satisfies* this predicate, and is the only one that does

Suppose that for predicates P and Q, the type of
_X_ is string. You can then *apply* either predicate,
P or Q, to a string to get a resulting proposition.

For example, (Q "Kevin") produces the proposition,
Kevin Sullivan is from Charlottesville, while (e3 2)
produces the proposition 2 = 3.  

Again, you can think of a predicate as a function: one that
takes values of given types as arguments and that returns
a *proposition* with the argument values plugged in where
the predicate had its parameters. A predicate really is
like a function that returns a proposition: it takes one
or more values as arguments, and returns a proposition that
makes an assertion *about* those values.

### Predicates as functions

Speaking more formally, we represent a predicate exactly
as a function, from parameter values to propositions. In
the case of the predicate e3, it's a function that takes
a natural number, n, and returns the proposition, n = 3:
a proposition about n. Here's how we might define this
predicate/function in Lean.

def e3 (n : nat) : Prop := n = 3

The syntax is pretty simple. First, def introduces a
new definition. What's being defined to have a value is
e3. The argument/parameter is a value, a natural number,
n. And what the function then returns is the proposition,
n = 3, for any value of n that is given as an argument.

Applying e3 to 2, for example, yields the proposition,
2 = 3. This proposition is "about 2" in the sense that
it claims (falsely) that 2 has the property of being equal
to 3.

## Constructing equality proofs (introduction rule)

You've already learned the reflexivity axiom
for equality: ∀ (T : Type) (t : T), t = t.

This axiom provides a way to *construct* proofs
of equalities. If you "give it" a T and a t, it
gives back a proof of the proposition that t = t.

Such a proof-building axiom is said to be an
*introduction* rule (here, for equality). More
generally, introduction rules define mechanisms
that *construct* proofs of given kinds (e.g., of
equality propositions).

## Using equality proofs (elimination rule)

We now turn to the second of the two axioms that
define equality: the *substitutability of equals*.

### The intuition

This axiom basically states that if you know that
some object, x, has property P, and you also know
that x = y, then you can conclude that y must also
have property P (because y *is equal to* x)

Example. If "Kevin is from Cville" and Kevin is
really just an alias for Bob (Kevin = Bob), then
we can deduce that "Bob is from Cville."

Example: If we know that (x + 2) = 7, and we also
know that "x = y," then we can deduce that (y + 2)
= 7.

In other words, the second axiom gives us a license
to *rewrite* propositions by replacing one term with
another as long as we can provide a proof of equality
of those two terms as an argument.

### Formal statement of the axiom of substitutability

Here's a version of the axiom presented in language
of predicate logic conforming with the syntax of Lean.

``` lean
axiom eq_subst :    -- arguments are assumptions!
  ∀ (T : Type)      -- if we're given, T, a type
    (P : T → Prop)  -- P, property of T objects (predicate)
    (x y : T)       -- x and y, objects of type T,
    (e : x = y)     -- e, a proof of x = y (we *use* an = proof)
    (px : P x),     -- a proof that x has property P
  P y               -- then we can have a proof of P y
```

Given any type, T, ... and any *property*, P, of objects
of this type, (P : T \to Prop), ... if you know that an
object, x, of type T, has property P, i.e., (P x) and you
know that x = y, then you can deduce P y: that it must be
the case that y has property P, as well.

### Example using substitutability axiom

Let's do a completely abstract example first. We
can use the axiom keyword in Lean to introduce a
set of assumptions.  

``` lean
axioms
  (T : Type)        -- assume T is a type
  (P : T → Prop)    -- P is a property of Ts
  (x y : T)         -- x and y are Ts
  (e : x = y)       -- e is a proof of x = y
  (px : P x)        -- px proves x has property P
```

From these assumptions, can we prove P y? Indeed
we can, because what we've assumed are exactly all
of the argumented required to apply the axiom of
substitutability of equals. Here then is a formal
proof that, from the preceding axioms, we can prove
(P y).

``` lean
example : P y := eq_subst T P x y e px -- Whoa
```

English: From the assumptions that P x is true,
and x = y, we can deduce that P y must be true
by applying the axiom of the the substitutability
of equals. (Try to come close to memorizing that
while visualizing what it really means.)

## Theorem proving

In this final section, we use the case of equality
to illustrate what we mean when we talk about proving
theorems. Here, from only the axioms of reflexivity
and sustitutability, we prove that equality has two
more crucial properties: symmetry and reflexivity.

In each case, we will construct a proof by first
using substitutability to rename variables in the
proposition to be proved so that we can then either
apply reflexivity, or point out that we have already
assumed what remains to be proved, so we are done.
We have constructed the desired proof.

### Theorem: Equality is symmetric

Theorem: the equality relation (on objects of
any given type) is symmetric.

To prove that equality is symmetric, we must
prove that, for *any* objects, x and y (of a
given type), if x = y then y = x.

Proof. We start by *assuming* that x and
y are objects of some type T. We also then
assume that x = y. On the assumption that
this is true, we must show is that y = x.
But by the substitutivity of equals, y = x
can be rewritten to y = y, *using the fact
that x = y*. The only thing that remains to
be proven now is that y = y, but that is an
easy proof by the reflexivity of equality.
QED.

Here's a less verbose proof.

Proof: By the substitutability of equals,
we can rewrite y = x as y = y (without any
change in meaning), but then this proposition
is true by the reflexivity of equality, so
the original y = x must be true as well. QED.

Here's another way.

1. T is a type               assumption
2. x and y are of type T     assumption
3. x = y                     assumption
4. y = x                     goal
5. y = y                     substitutability using 3
6. QED                       reflexivity

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
is something we've already assumed is true.

Or, if you prefer, in this last step, we can
use the assumption that y = z to apply the
axiom of the substitutability of equals to
rewrite the y in y = z to z, yielding z = z.
And that is proved from the reflexivity of
the equality relation on any type of objects.
QED.

## Conclusion

What you have now seen is the essence of a logical
argument (proof). We start with given axioms (such
as the reflexivity and substitutability of equals),
and from them we then deduce (construct proofs of)
new facts (such as the symmetry and transitivity
of equality). This is how all of mathematics works!
"Big" theorems are derived from axioms, "smaller"
theorems, and other values by the application of
inference rules that are themselves accepted as the
fundamental axioms of a given mathematical logic.
