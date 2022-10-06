section pred_logic

variables X Y Z : Prop

/- Under Construction -/

/-
And for this explanation, we need to be precise about what it means
to be a predicate in predicate logic. As we've exaplained before, 
a predicate is a proposition with one or more parameters. Think of
parameters as blanks in the reading of a proposition that you can
fill in with any value of the right type for that slot. When you 
fill in all the blanks, which you do by by applying the predicate
to actual parameter values, you get back a proposition: a specific
statement about specific objects with no remaining parameters to
be filled in. A predicate thus gives rise to a whole *family* of 
propositions, one for each possible combination of argument values. 
Once all the parameters in a predicate are fixed to actual values,
you've no longer got a predicate but just a proposition. 
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





