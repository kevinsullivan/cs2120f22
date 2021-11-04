# Theorem: Congruence mod n is an equivalence relation

In class today, we formally stated, and proved, that congruence mod n (for n : \Z) is an equivalence relations. Its proof uses and introduction to combine separate proofs that it is reflexive, symmetric, and transitive, respectively. See lecture_22.lean. The proofs are mostly unfolding definitions and (thankfully automated) proving of algebraic equalities between terms that use + and \* operators that satisfy all of the usual properties, e.g., associativity, commutativity, with usual rules for left and right distribution of \* over +.

This kind of structure algebraic structure is easily definable for integers, for rationals, for reals. Most of us learned this structure with the usual + and \* operations for real numbers. But you can do the same thing for rationals, integers, etc. That is, there are (in fact many) different versions of this common structure depending on the kinds objects/values are being operated on. The particular algebraic structure at issue here, abstracted from details of the type of the underlying objects, is called a "ring." Think of a certain type of numbers as the objects (e.g., naturals, integers, rationals, reals, complex, etc), with binary addition and multiplication operations define on these objects in a way that ensures that the ring axioms are satisfied.

In class today, whenever we got to the point where we needed to reason *algebraically* to prove such equality propositions, we just said "sorry; to us it's so clearly true so we'll just accept is as an axiom using sorry." That's fine if it's what're being accepted as axioms are not only obviously but also really true. 

The problem is that these things get subtle fast. All else being equal we'd certainly prefer to have foundational proofs for every proposition that we ever accept as being true. What would be wonderful would be for the machine to "automatically reason" using the axioms of a given theory (e.g., that of rings) do just "do whatever algebra is needed to try to simplify the given expressions to some kind of lowest ("normal") form. Again, the axioms here (for rings) just say things like "for any objects a and b, a + b = b + a."

Now a common problem in finishing off a proof is to show that two algebraic expressions are equal: for example that (x + y) * (x + y) = x2 + 2xy +y2. If both arguments of = reduce to the same term (which they do here), then the rest is just by the reflexivity of equality.

To prove such an equality might take quite a bit of manipulation of the two sides of the equation. You can always do it manually, applying sequences of low-level theorems (e.g., about commutativity and associativity of +), but such low-level proof programming can be tedious and tiresome.

Enter automated reasoning. Automated reasoning (AR) is the application of computerized procedures to at least partially automate the construction of proofs of suitably restricted forms of expressions in predicate logic. Decision procedures determine whether a given proposition is true or not, but only for precisely restricted forms of propositions. As a first example, I have now completed *completed* the formal proof that congruence mod n on the integers is an equivalence relation.

The trick was to use a Lean "tactic" that implements a normalizing function for algebraic expressions using + and \* operations that satisfying the basic rules of arithmetic. It solves proof construction problems that you'd otherwise have to handle yourself. Please step through the proofs, which are just as we left them in class, but now watch the *near magic* of automated proof construction. Sometimes one has to help things along a little, and you'll see that too, here.

What you now have is a mechanically verified foundational proof of the following theorem.

Theorem: Congruence mod n on Z is an equivalence relation.
Proof: Yeah, we really have one!

Please take some time to go over and study this material over the weekend, if you can. Try to see that *you* could have figured out how to produce the proof that we went over in class today, at least up to the points where you needed proofs of ring-algebraic equality propositions. Now in one fell swoop, thanks to automated proof production, you now have another whole "language" in which to write and prove propositions: the algebraic language of rings. *And* you get amazing proof automation in rings to go with it!

End note: We imported the ring-related tactics from Leans mathlib and used the "ring" tactic, one of several ring-related automated reasoning tactics.
