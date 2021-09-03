# Inductive families

As a different example, consider the property of being
an *even* natural number. The corresponding predicate,
let's call it Ev, is the "proposition with a parameter,"
"_X_ is even," where _X_ can be any natural number.

Applying Ev to the argument, 7, say, will yield the
proposition, Ev 7. It asserts that "7 is even" or "7
has the property of being even."

A predicate is meaningful when it captures a property
of interest. To capture of property, such as that of
being even, it must be the case that every proposition
produced by applying the predicate to an even number is
true, and every proposition applied to any other number
is false.

As with proofs and other aspects of mathematical logic,
we can be formally precise in defining predicates, or
we can use precise English language in cases where we
can reasonably assume that readers will know exactly  
what we're saying. For example, we could be informal,
and say, "Let Ev be a predicate that expresses the
property of being an *even* (natural) number." What we
have left to intuition here is the precise definition
of what it means to be even.

If we wanted to be more formal, we might define what
it means to be a proof that a given number, say x, is
even. In a sense, we need some *axioms* that tell us
for what values of x we can produce a proof of Ev x.
Here's are two such "axioms" stated quasi-formally.

- axiom e0 : Ev 0
- axiom en2 : forall n, Ev n -> Ev (n + 2)

The first axiom says "assume that we have a proof, e0,
that "0 is even" (remember, Ev 0 is the predicate Ev
applied to the value 0 yielding the proposition Ev 0
that we understand to represent the claim that "0 is
even".) The second axiom says that for any value, n,
if n is even then (n+2) is even. The result of these
two rules put together is that we have proofs of the
propositions,

- Ev 0, zero is even
- Ev 2, two is even
- Ev 4, four is even
- ad infinitum!

Moreover, if we want to prove that a number, x, other
than zero is even, it *suffices* to prove that the
number two less than x is even, because if it is,
then the second axiom lets us deduce that x is even.

Example: Give a proof that 6 is even.
Proof: It suffices to prove that 4 is even, because if
it is then (4 + 2) is even by the second axiom. So now
all we have to prove is that 4 is even. To prove that,
it will suffice to prove is that 2 is even (for the same
reason). And to prove that 2 is even, all we have to
prove is that 0 is even. But we're give a proof of
that by the first axiom. QED.



