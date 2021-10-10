/-
THe file extends what you have learned by
introducing the concept that existential
quantification is an "information hiding"
abstraction mechanism. To build a proof
of ∃ x, P x, you have to give a specific 
value for x; but when you eliminate from 
a proof of ∃ x, P x, all you get is some
arbitrary but specific value, along with
a proof that that value has property, P.
The specific value that was used to build
the proof is no longer available by use of
exists elimination. Let's see this idea in
action.
-/

/-
We represent a *property* objects of a 
type, α, as a *predicate* on α values. 
Here, e.g., is a one-place predicate on
natural numbers. It is satisfied by any
natural number n such than n % 2 is zero.
-/

def ev (n : ℕ) : Prop := n % 2 = 0
#check ev   -- nat → Prop

/-
Here's a silly theorem that says that
if one assumes (that one is given) a
natural number, n, and proof, pf, that
n satisfies ev ("n is even"), then you
can prove that *there exists* an even
number. The proof uses n itself as the
witness, and pf as the proof, arguments.
This example is meant only to remind
you about the introduction rule for ∃.
-/
theorem 
ex_ev_n (n : ℕ) (pf : ev n) : 
  ∃ (m : ℕ), ev m := 
  ⟨ n, pf ⟩   -- exists.intro n pf


/-
And now that we've prove this theorem, 
in the form of a universal generalization
(!), as it takes *any* natural number, n, 
as long as a proof of ev n, *for that n*, 
can also be provided. You can even think
of this theorem as function that can only
be called with any even number, m, and 
that when so called returns a proof that 
there exists an even number, from which m,
itself, can no longer be obtained.
-/

/-
Here's a proof that there exists an even
number; but where the 4 is not recoverable
by elimination of the overall proof term.
-/

#check ex_ev_n 4 rfl 

/-
Four happens to be the witness used to build
a proof of ∃ x, ev x, in this case; but from
that proof one cannot recover the value, 4. So
now let's unpack this fact into more detail.
-/

/-
In this example, we show off the information
hiding, or abtracting, functionality of exists.

You (constructively) prove ∃ x, P x by giving
a specific value for x along with a proof of 
P x. Here's where the abstraction, or hiding
of details, happens: when you "eliminate" a
proof of an existential proposition, you get
back an arbitrary value, w, as a witness, and
not the specific value that was ostensibly
provided when the proof was constructed. 

Details go in, but they don't come back out.
A proof of an existential affirms that such
an object exists but cannot tell you exactly
which one. Still, in constructive logic, if
you have a proof, then you can infer that some
specific object/value must have been provided
to exists.intro. The exists.elim rule allows
you to *assume* an object and a corresponding
proof, giving names to each one. As you will
see (again) next, applying exists.elim using
the "cases" tactic has exactly this behavior. 
-/

/-
In this example we prove (∃ x, P x -> true) so that
we can assume ∃ x, P x. Our aim isn't to prove true,
but to see exactly what we get when we "eliminate" 
from an assumed proof of ∃ x, P x. And the answer, 
as we've explained, will be an arbitrary but specific
value *now with a name, w*, along with a proof of the
proposition, (P w). 
-/
example : (∃ (m : ℕ), ev m) → true :=   
begin
  assume h,           -- get ourselves proof of ∃ 
  cases h with w pf,  -- what case analysis does: 
                      -- one intro rule, one case,
                      -- with info about the args,
                      -- but no witness *details*.
  trivial,
end
/-
As you now understand, the cases "tactic" applies 
the elimination rule for the given form of value.  
So, here, it applies or.elim (and a few clean-up
tactics). Put your cursor at the end of the cases
line and study the resulting context. You now have
a witness, w, of the right type, but you do not a 
specific value. You have some arbitrary value of 
the given type except it's one for which you also
have a proof that it satisfies the given predicate.
-/

/-
The constraint that the elimination rule doesn't
reveal the witness, once it has been abstracted
away, is enforced by Lean's type system. Let's 
see what happen if we try to recover the natural
number, m, "inside" a proof of (∃ (m : ℕ), ev m).

Notice the crucial difference in the type of the
following implication/function. Where above we 
wanted a proof of (∃ (m : ℕ), ev m) → true, a 
purely logical proposition, how we're trying to
produce a proof of (∃ (m : ℕ), ev m) → nat.
This would be a function that takes a proof of
an existential proposition as an argument and 
that somehow then comes up with a natural number
to return (rather than true.intro) as a result.

It'd be possible to implement this function if 
one could recover the witness used to create a
proof of ∃ x, P; but it's not. Lean complains
that you are trying to eliminate from a proof 
to a value of a type, T, where T is not Prop.

What Lean is really preventing you from doing
is *computing* with values extracted from the
proof of a logical proposition. This restriction
in turn is part of its approach to assuring the
principle of proof irrelevance. Any proof is 
equivalent in all respects to any other. If we
could get a 4 from one ∃ proof and a 5 from 
another, then this principle would break, as 
having one or the other proof would lead to two
different computations. That's not allowed.
-/

example : (∃ (m : ℕ), ev m) → nat :=   
begin
  assume h,           -- get ourselves proof of ∃ 
  cases h with w pf,  -- here's where you get caught
  trivial,
end

/-
What Lean is saying is that it's alright from a
proof of (∃ (m : ℕ), ev m) to derive a proof of
true, because true lives in the type, Prop. On
the other hand, nat lives in the type, Type, and
the rules of predicate logic do not allow one to
recover a computationally relevant value from a
proof of ∃ x, P. (I'm dropping the P x notation.)
In this way Lean enforces the abstracting nature
of existential quantification.
-/