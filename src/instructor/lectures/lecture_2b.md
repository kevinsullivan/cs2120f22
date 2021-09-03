# Equality

We can understand a lot about predicate logic by
understanding seemingly trivial but actually very
rich concept of equality.

There are two things that we all understand intuitively. The most intuitive thing is that everying is equal to itself. Or, in more type theoretical terms, every thing of every type is equal to itself. 

In set theory, there is only one type of object, and all  other distinctions are made by predicates. In type theory, every object belongs to one type; arbitrary types can be defined; and type errors in expressions are detectable by a (an efficient) type checking algorithm.

## - To understand a logic

To understand a logic requires the following ingredients:

- The *syntax* of the formal language in which propositions are expressed
- What constitutes a *proof* in that logic
- The *inference rules* by which:
  - proofs of "larger" propositions can be constructed from values that can include proofs of "smaller" propositions
  - how proofs and other "values" can be used in the definitions of these rules
- How to apply the inference rules of a logic to turn arguments into new proofs

## Equality propositions

Many different logics include a notion of equality. They provide syntax to express propositions of the form, x = y; ways to produce proofs that such propositions do hold; and ways to use proofs to enable a fundamental transformation of proofs of propositions of the form P x into propositions of the form P y, licensed by the fact that we know (the truth, and that we have a proof, of) x = y. In other words, the way to use a proof of an equality is as an argument to the second inference rule for equality, which allows substitutions of equals for equals in arbitrary we'll sometimes write as *eq x
y*), will enable reasoning about when certain things referenced in different ways (here as x and y, respectively) are actually the same things. In a short, equality is a concept supported by many many different logics.

example : Prop := 

Equality propositions are claims that two quantities are equal to each other. Here are a few examples:

- 1 = 1 (a little vague about the type of "1")
- 1.0 = 0.1 * 10 (is this always true?)
- 0 = 1 (not all propositions have proofs or are true)
- 1 + 1 = 2 (different expressions but same values?)
  
## Produce a proof of an equality proposition


- A set of inference rules is sound when they cannot derive a contradiction
- A set of inference rules is complete when every true proposition has a proof
- A logic accepts some set of inference rules as assumed to true: as *axioms*
  
- To understand a given logic you must understand its axioms and
- Let's look again at something as seemingly simple as equality
  