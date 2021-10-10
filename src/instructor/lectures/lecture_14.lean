/-
Note this this file is called lecture 14,
though today, October, 6, is more than 14
course days in. The reason is that the last
two days were review Q&A in preparation for
the mid-term.
-/

/-
REVIEW INTRODUCTION AND ELIMINATION RULES FOR EXISTS.
-/

/-
LET'S PROVE A THEOREM INVOLVING EXISTS, ALL, AND NEGATION
-/


/-
Is it true that if not everyone likes themselves
then there is someone who doesn't like themself?
-/

/-
Challenge #1: Set up the domain model and then
express the proposition about it. In this case,
the domain model includes people and a binary
likes relation "over" people.
-/
axioms 
  (Person : Type) 
  (Likes : Person → Person → Prop)

example : 
  ¬ (∀ p : Person, Likes p p) ↔ 
  ∃ p : Person, ¬ Likes p p :=
begin
apply iff.intro,
-- forward
assume h,
have f := classical.em (∃ (p : Person), ¬Likes p p),
cases f,
-- case #1: there IS someone who dislikes themself
  assumption,
-- case #2: there IS NOT someone who dislikes themself
-- propose new fact, proof to be constructed in this context
  have contra : ∀ (p : Person), Likes p p := _,
-- prove current goal using proposed fact
  contradiction,

-- still have to prove supposition
assume p,

-- same trick again!
have g := classical.em (Likes p p),
cases g,
assumption,
have a : ∃ (p : Person), ¬Likes p p := exists.intro p g,
contradiction,
-- backward
assume h,
cases h with p l,
assume a,
have d := a p,
contradiction,
end

theorem not_all_iff_ex_not : 
  ∀ (T : Type) (R : T → T → Prop), 
  ¬ (∀ t : T, R t t) ↔ ∃ t : T, ¬ R t t 
  :=
begin

end




