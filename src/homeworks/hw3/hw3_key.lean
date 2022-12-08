/-
CS 2120 HOMEWORK #3
OUT: SUN, SEP 25
DUE: MON, OCT 3

PURPOSE: The purpose of this homework is to help you understand
the material covered up to now on first- and higher-order predicate
logic. There are four questions. Each samples your understanding of
multiple concepts. You might have to put different ideas from our
work together to fully answer the questions. Give yourself time to
think about this material. 

INSTRUCTIONS: Read and follow the instructions for each question,
below. Edit all of your answers into this file. That's what you'll
turn in.

COLLABORATION: You may communicate with each other in general terms
about the material we've covered but you are NOT to give or receive
specific answers, or hints strong enough to essentially give away any 
answers, on this homework. Please, do yourselves and your colleagues
a favor and don't tell or take answers. This homework is a key check
on, via preparation for, an upcoming midterm exam.  

NEED HELP: Please don't post answers or partial answers on Piazza or 
any other forum that would substantially give away any part of the 
answer to any of these questions. That said, freely post any questions
you might have, and feel free to offer general answers to questions 
from others, on Piazza. TAs answer at least several times a day. 
Attend office hours: Wednesday and Sunday night 7-10. Talk to Sullivan. 
If you feel deeply lost, email Prof. Sullivan ASAP to for help on how
best to proceed. 
-/

/- #1: Logic to English 

Read through the new material in 09_20_22_inference_rules.lean, which
starts on line 264. After reviewing our all balls blue example, it then
presents an English-language rendition of our "demonstration" that if 
all balls are blue and if b1 and b2 are balls then b1 is blue and b2 
is blue. Compare the English language proof with the formal version, 
paying attention to how we named and specified the proof that all balls
are blue. 

Continue reading through our formalized version of the story that 
everyone is mortal and so is Socrates so Socrates is mortal. Now 
write an English-language version of the proof, using the model from 
the earlier case of "all balls blue." Don't just do it mindlessly: 
really think about what you're saying with each word in your proof. 
See how the English presents the "story" of the formal proof in more
natural, human, terms.

ANSWER HERE: 

Here's the formal proof:
-/

variable Person : Type
variable Socrates : Person
variable isMortal : Person → Prop
variable everyoneIsMortal : ∀ (p : Person), isMortal p
#check (everyoneIsMortal Socrates)   -- ∀ elimination!

/-
Suppose that Socrates is a person and that isMortal is
a predicate taking a person, p, as an argument and
yielding a proposition, (Mortal p), that we interpret
as meaning that P is mortal. Next assume that everyone
is mortal. Our goal is to prove that Socrates is mortal.
But this follows simplying by applying the universal
generalization, that everyone is mortal, to the specific
person, Socrates, to conclude that Socrates is mortal.  

KS: Review arrow and ∀ elimination.
-/

-- ∀ elimination example
example : 
  ∀ 
    (P : Type) 
    (S : P → Prop) 
    (ug : ∀ (p : P), S p)
    (p : P), 
  S p :=
begin
assume P S ug p,  -- assume we're given arguments
exact (ug p),     -- universal elimination proves (S p)
end 

-- → elimination example
example :
  ∀ 
    (P Q : Prop)
    (i : P → Q)
    (p : P),
  Q :=
begin 
  assume P Q i p, -- assume we're given arguments
  exact (i p),    -- arrow elimination proves Q
end 


/- #2: English to Logic 
Formally model this natural-language "logic story" in Lean, using
the material we covered in the lecture notes as a model. Here's the
story.

If one person likes a second, and the second likes a third, 
then the first is jealous of the third. Hint: model "likes" and 
"isJealousOf" as two two-place predicates.

Now suppose Ed, Hannah, and Mel are people, and that Ed likes 
Hannah, and Hannah likes Mel. Write, and use #check to check, an
expression that proves that Ed is jealous of Mel. Uncomment the
following block of expressions then fill in blanks to complete
this task.
-/

-- variable Person : Type                      -- already defined
variable Likes : Person → Person → Prop        -- a predicate with two Person arguments
variable Jealous : Person → Person → Prop      -- same thing here  
variable Triangle :                            -- note definition extends to next line
  ∀ (p1 p2 p3 : Person), Likes p1 p2 → Likes p2 p3 → Jealous p1 p3  
variables ed hannah mel : Person
variable likes_ed_hannah : Likes ed hannah
variable likes_hannah_mel : Likes hannah mel
-- Finally write and use #check to check an expression that proves that ed is 
-- jealous of mel.
-- TO ANSWER WRITE YOUR EXPRESSION IN PLACE OF THE _ THAT COMES NEXT. 

#check Triangle             -- we'll work out the rest in class review


/- #3: Proofing a propositions involving ∀ and ∨

Write an English-language  proof of the following proposition, using
the methods of inference we've covered. ∀ (P Q : Prop), P ∧ Q → Q ∨ P. 
Do read that proposition carefully, please.

PROOF: LET P AND Q BE ARBITRARY BUT SPECIFIC PROPOSITIONS. TO PROVE
P ∧ Q → Q ∨ P, ASSUME P ∧ Q AS A HYPOTHESIS. BY AND ELIMINATION WE  
DEDUCE P AND Q. WE NOW PROVE Q ∨ P BY OR INTRODUCTION ON EITHER SIDE.
Note that there are two ways to prove the result! We treat any proof
as equally as good as any other.
-/


/- 
Express the following proposition formally. Introduce whatever types, values, 
predicates, etc., you need as in the several examples in the classwork. If you
have already defined a term above, don't repeat it here. Here's the claim you
are to formalize: Everyone knows someone who knows someone who knows everyone.
-/

-- variable Person : Type                 -- defined above
variable Knows : Person → Person → Prop
def foo : Prop := 
    ∀ (P : Person), 
      (∃ (Q : Person), 
        (Knows P Q ∧ 
          ∃ (R : Person), 
            (Knows Q R ∧ 
              (∀ (T : Person), 
                Knows R T
              )
            )
        )
      )