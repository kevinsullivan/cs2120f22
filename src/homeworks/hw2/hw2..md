# Homework #2 Propositional Logic Modulo Theories

This homework is meant to prepare you for the first part of the mid-term exam, on *propositional logic.*

Pure propositional logic is tantamount to a language of Boolean expressions, in which all variables are Boolean, larger expressions are build inductively from variable expressions and any of several connectors: and, or, not, implies, bi-implication. A proposition in pure propositional logic has a number of interpretations exponential in the number of its variables. Such an expression is valid, satisfiable, or unsatisfiable, respectively, if all, at least one, or none of its interpretations is a model. Recall that a model is an interpretation, assigning concrete solution values to each of the variables.

- It includes propositional logic, in which all variables are Boolean, and in which we interpret logical connectives (and, or, not, etc) as their corresponding Boolean functions (e.g., &&, ||, and ! in C.)
- It supports *algebra* involving more than just Booleans. Z3 variables can be integer, real, and more. You write logical propositions (now viewed as "constraints" on an aceptable solution) involving such variables, and, if you're lucky an SMT solver, such as Z3, will be able to find you a solution if there is one.

Now we can write propositional logic expressions such as *(x < 8) and (x > 6)*. The idea is that any value that satisfies the two constraints, *x is less than 8* and *x is more than 6* is a solution. You can take it from there!

More than that, we've seen that if we can express constraints as propositions in propositional logic (plus Z3 arithmetic and the like), then it's straightforward to translate these propositions into expressions in Z3, which can then often be used find satisfying solutions.

Not only that, but if your constraints languages are limited enough, then we might even have "solvers" (decision procedures) for them. That means at least two great things for the software engineer or theorist: (1) such languages are often good for writing *specifications* for what procedural code must do; (2) if good solvers do exist, then all you have to do to solve a problem is express it declaratively in the given logic and let the solver find a solution.

Going forward, however, we'll sometimes need logical languages are more expressive than the propositional logics we've been exploring up to now.
