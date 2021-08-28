# Truth and Reasoning

## Truth

We do better on the whole when we act on what is _true_ than when we don't.

## Reasoning

- Cognitive paths to truths
- Important styles of reasoning include inductive, abductive, deductive.
  - Inductive:
    - The sun has always come up in the morning, so (generalizing from these observations leads one to predict that) it will come up again tomorrow, too.
    - Idea: derive generalized predictive models from given sets of observations
      - choose/use a reasonable form of model (e.g., y = mx + b)
      - calibrate m and b coefficients to get a minimum-error fit of line to data - test model by using it to predict results for previously unseen inputs
      - measure model prediction errors (e.g., |predicted_price - selling_price|)
      - update generalization: feed back error to improve the model coefficients
    - Is this form of reasoning *sound* or *not sound*? Briefly explain.
  - Abductive
    - An example from class:
      - On trying to clone repo in container, no GitHub URL was requested
      - We did online search then guessed it was that git was missing but required
      - Experiment: Install Git for Windows; reboot; expect problem to be solved
      - Outcome:
        - Problem was solved!
        - Hypothesis appears confirmed. (That's abductive reasoning.)
    - Based on whatever information you have or can get, *guess* a good hypothesis
    - Test your hypothesis experimentally and adjust your trust in it accordingly
  - Deductive
    - Assume that certain given propositions (axioms) are true (or have proofs)
    - Combine truths/proofs of smaller propositions into truths/proofs of bigger ones
    - Formal rules of inference define how truth or proof values can be combined
    - Examples:
      - If you know propositions P, Q, are true, you can deduce "P AND Q" is too
      - If you have proofs of P, Q, you can construct a bigger proof: of "P AND Q"
      - A proof shows a proposition to be true, but also explains _why_ it's true
      - A truth value provides a single binary digit (bit) of information, the smallest amount possible; while a proof can provide petabits of explanation
- The deductive style is at the heart of mathematics and classical computer science
  - Their rules of evidence require _proofs_ to decide the truths of propositions
  - Inductive reasoning is at the heart of various *deep learning* methods in AI
  - Debugging is rooted in abductive reasoning: *guess* the bug then test the guess

## Example: Prove 1 = 1

Theorem: 1 = 1 (where 1 is a natural number)

Proof: By application of the *reflexive axiom of equality*. This axiom, part of most definitions of predicate logics, states that every object, t, of every type, T, is equal to itself. We write this formally in the syntax of the predicate logic we will use in this class, as follows: 

``` lean
∀ (T : Type) (t : T), t = t .
```

Given that the axiom stipulates that every object of every type is equal to itself, and given that 1 is an object of some type (ℕ), it must be that 1, _in particular_, is equal to itself. This reasoning allows us to deduce not only that 1 = 1 is true, but we now also have a precise explanation why that is the case. This particular example of reasoning is called *universal elimination*.

## The rest of this lesson

The rest of this lesson is in the file, lecture_1.lean. There, we further discuss and give examples of formal proofs and quasi-formal (natural language) "proof descriptions." We take proofs of equality propositions, such as 1 = 1 or 1 = 2, as examples. We'll go deeper into the concepts of propositions, axioms, proofs, logical truth, and the idea that we can understand logical reasoning as a form of computation involving propositions and proofs as types and data values, respectively. We also briefly review number systems as well as styles of reasoning and the concept of soundness. Part of this review is in the form of a short quiz at the end of the next file.
