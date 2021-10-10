/-
This file is being distributed on the last evening before
our UVa 2021 fall break. We have already discussed exists
introduction and elimination in class. THe file extends 
what you have learned by introducing the concept that the
exists introduction rule is an "abstraction mechanism."
-/

/-
We represent a *property* objects of a type, α, as a 
*predicate* on values of this type. 
-/

def ev (n : ℕ) : Prop := n % 2 = 0

theorem 
ex_ev_n (n : ℕ) (pf : ev n) : 
  ∃ (m : ℕ), ev m := 
exists.intro n pf

-- a proof that there exists an even number
#check ex_ev_n 4 rfl
/-
Four happens to be the witness used to build
a proof of ∃ x, ev x; but neither from that
proof or from any other ∃ proof, can a recover
of obtain a precise withness back. 
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
provided when the proof was constructed. So
details go in, but they don't come back out.
A proof of an existential affirms that such
an object exists but cannot tell you exactly
which one. Still, in constructive logic, you
know that some specific object must have been
provided to exists.intro.
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