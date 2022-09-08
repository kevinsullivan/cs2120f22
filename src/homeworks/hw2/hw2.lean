/-
Below we've listed eleven proposed "inference rules." Remember
that such a rule has a context, which is a list of propositions
that you already know, or assume (hypothetically) to be true; then
there is a turnstile symbol (⊢), which you can read as "entails"
or "makes it logically necessary that"; and finally to the right
of the turnstile is a conclusion. 

Such a rule can be read both left to right and right to left. Left
to right, it says that if all of the conditions on the left (in the 
context) are true, then by applying the rule you can conclude that 
the conclusion, after the turnstile, is also true. Reading right to 
left, on the other hand, it says that if you want to show that the
conclusion is true, then it is sufficient (suffices) to show that
each of the propositions on the left is true; because if all those
propositions are true, then you can apply the rule to deduce that
the conclusion must be, too.

An inference rule is meant to express a *valid* rule of reasoning
in general. To be valid, such a proposition must be true no matter 
what specific values are assigned to the variables. Most of these 
proposed rules are valid, but to make things interesting, we have
thrown in a few *fallacies*, which are seemingly sound but actually
invalid rules. 

Your goal is to understand both intuitively and formally which of 
the rules below are valid, and which are not. To this end, for each 
proposed rule, do the following:

- Translate the rule into English. For example, for the first 
rule you could write, "If X is true, and if Y is also true, then
it is logically necessary that X ∧ Y is true." You might find it
helpful to express X → Y as "whenever X (is true), Y must be, too."
For example, you might translate "Raining → Wet" as "whenever it's
raining, it's also wet," or "IF it's raining, THEN it's wet."
-  State whether you believe the rule to be valid or not valid.
- Encode the rule in Z3 and check it for validity. To do this
you can translate each context into a conjunction of its elements,
and you can translate ⊢ into propositional logic as →. For example,
you an translate the "and introduction" rule (second below) into 
X ∧ Y → X ∧ Y. If Z3 confirms that your rule is valid, you're done.
- For any rule that's not valid, have Z3 return a counterexample, 
and translate the formal counter-example into a concrete example 
in English and explain why it doesn't make sense.
-/

/-
- X ∨ Y, X ⊢ ¬Y             -- affirming the disjunct
- X, Y ⊢ X ∧ Y              -- and introduction
- X ∧ Y ⊢ X                 -- and elimination left
- X ∧ Y ⊢ Y                 -- and elimination right
- ¬¬X ⊢ X                   -- negation elimination                    
- X ⊢ X ∨ Y                 -- or introduction left
- Y ⊢ X ∨ Y                 -- or introduction right
- X → Y, ¬X ⊢ ¬ Y           -- denying the antecedent
- X ∨ Y, X → Z, Y → Z ⊢ Z   -- or elimination
- X → Y, Y ⊢ X              -- affirming the conclusion
- X → Y, X ⊢ Y              -- arrow elimination
-/

/-
Hint: Recall that s.check() returns sat or unsat, and that
there's an easy "trick" to use Z3 to determine if a given
proposition is *valid*. Write (or just copy from class) a 
simple procedure that takes any proposition, C, and returns
true if it's valid and false otherwise. You need to check 
each proposition above for validity, so you will find it
helpful to have this helper function in your code so you
can just call it.
-/

/-
What to turn in.

Turn in ONE Python file. 

HINT: Once you've added constraints to a Solver, s, and used
s to try to satisfy the constraints, you can then use the 
s.reset() method to clear the solver for the next set of 
constraints to be checked/solved.
-/