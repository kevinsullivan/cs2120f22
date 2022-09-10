/-
Below we've listed 20 proposed "inference rules" for reasoning 
with propositional logic. Remember that such a rule has a context, 
which is a list of propositions that you already know, or assume 
(hypothetically), to be true; then there is a turnstile symbol (⊢),
which you can read as "entails" or "makes it logically necessary
that"; and finally to the right of the turnstile is a conclusion. 

Such a rule can be read both left to right and right to left. Left
to right, it says that if all of the propositions on the left (in 
the context) are true, then by applying the rule you can conclude 
that the conclusion, after the turnstile, is also true. Reading 
right to left, on the other hand, it says that if you want to show
that the conclusion is true, then it is sufficient (suffices) to
show that each of the propositions on the left is true; because if
all those propositions are true, then you can apply the rule to
deduce that the conclusion must be, too.

An inference rule is meant to express a *valid* rule of reasoning
in general. To be valid, such a proposition must be true no matter 
what specific values are assigned to the variables. Most of these 
proposed rules are valid, but to make things interesting, we have
thrown in a few *fallacies*, which are seemingly sound but actually
invalid rules. 

Your goal is to understand both intuitively and formally which of 
the rules below are valid, and which are not. To this end, for each 
proposed rule, do the following:

- In the Python file you will turn in, translate each rule as given
here into a proposition in Z3 and assign that proposition to a 
Python variable called Cn, where n is 1-20 corresponding to the
enumeration below. For example, C3 = (Implies(And(X, Y), X). Note: 
translate each context into a conjunction of its elements, and then
translate ⊢ into propositional logic as →. For example, you can 
translate the "and introduction" rule below into X ∧ Y → X ∧ Y.  
- Below each such assignment, in comment, translate the rule into 
English. For example, for the first rule you could write, "If X ∧ Y 
is true, then it must be that X is true, as well." You might find it
helpful to express X → Y as "whenever X is true, Y must be true."
For example, you might translate "Raining → Wet" as "whenever it's
raining, it's also wet," or "IF it's raining, THEN it's wet."
-  State whether you believe the rule to be valid or not valid.
- Use Z3 to check each rule for validity. If Z3 confirms that your 
rule is valid, you're done. Your program should print "Cn is valid"
for that rule, where n is the rule number.
- For any rule that's not valid, have Z3 return a counterexample, 
and translate the formal counter-example into a concrete example 
in English and explain why it doesn't make sense. Put each such
English language translation in a comment under the statement of
the rule in Python.
-/

/-
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
Hint: Recall that s.check() returns sat or unsat, and that
there's an easy "trick" to use Z3 to determine if a given
proposition is *valid*. So DO write into your solution file 
a procedure that takes a proposition, C, and returns true if 
it's valid and false otherwise. You will need to check each
proposition above for validity, so you will find it helpful
to have this helper function, so that you only have to write
the code once. 
-/

/-
What to turn in.

Turn in ONE Python file that, when run, prints out one
line of output for each of the 19 problems, either saying
that the inference rule is valid, or that it's not and giving
a model that serves as a counterexample. HINT: Once you've 
added constraints to a Solver, s, and used s to try to
satisfy the constraints, you can then use the s.reset() 
method to clear the solver for the next constraints to be
checked/solved. Whenever you find a rule that's not valid,
given an English language example of a situation in which
it's not true. Add this explanation as a comment where your
code checks for validity.
-/