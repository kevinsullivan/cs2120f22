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
on, and preparation for, an upcoming midterm exam.  

NEED HELP: Please don't post answers or partial answers on Piazza or 
any other forum that would substantially give away any part of the 
answer to any of these questions. That said, freely post any questions
you might have, and feel free to offer general answers to questions 
from others, on Piazza. Our TAs answer at least several times a day. 
Attend office hours: Wednesday and Sunday night 7-10. Talk to Sullivan. 
If you feel deeply lost, email Prof. Sullivan ASAP to for help on how
best to proceed. 

WHERE TO SUBMIT: Assignment tab for HW#3 on Collab
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
write an English-language version of the proof,using the model from 
the earlier case of "all balls blue." Don't just do it mindlessly: 
really think about what you're saying with each word in your proof. 
See how the English presents the "story" of the formal proof in more
natural, human, terms.

ANSWER HERE:
-/


/- #2: English to Logic 
Formally model this natural-language "logic story" in Lean, using
the material we covered in the lecture notes as a model. Here's the
story.

If one person likes a second, and the second likes a third, 
then the first is jealous of the third. Furthermore, Ed, Hannah, 
and Mel are people; Ed likes Hannah; and Hannah likes Mel. 

Write, and use #check to check, an expression that proves that Ed 
is jealous of Mel. 

To do so, uncomment the following block of expressions then fill 
in blanks to complete this task.
-/

/- Uncomment this block to answer the question
variable Person : Type
variable Likes : _        -- a predicate with two Person arguments
variable Jealous : _      -- same thing here  
variable Triangle :       -- note definition extends to next line
  ∀ (p1 p2 p3 : Person), _  
variables ed hannah mel : _
variable likes_ed_hannah : _
variable likes_hannah_mel : _
-- Finally write and use #check to check an expression that proves that ed is 
-- jealous of mel.
-- To ANSWER, fill in the _ with your expression. 
-- HINT "Apply" what you know.
-/

#check _


/- #3: Proofing a propositions involving ∀ and ∨

Write an English-language  proof of the following proposition, using
the methods of inference we've covered: ∀ (P Q : Prop), P ∧ Q → Q ∨ P. 

Do read that proposition carefully, please. You don't need to write a
long proof. Keep it concise. Identiy the inference rules you use.

-/


/- 
Model the following logic story formally. Everyone knows someone who 
knows someone who knows everyone.

Note: As you've likely defined Person as a type in answering question
#2, you don't need to do it again here. Comment out the definition we
give you if it's redundant with your answer above. Give your answer
by writing the formalized proposition in place of the _ that follows.
You may (and probably should) break up your expression over several
lines, using line breaks and indentation to make the answer readable.
-/

variable Person : Type
variable Knows : Person → Person → Prop
def answer : Prop := 
    _
