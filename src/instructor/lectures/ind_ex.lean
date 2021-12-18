/-

Let P n := sum 0..n = n * (n+1) / 2.

Prove ∀ n, P n

By mathematical induction it will suffice
to show (P 0) and ∀ n', P n' → P (n'+1)

Proof of (P 0): Expanding P we have that 
sum 0..0 = 0*(0+1)/2. The left and right
sides both reduce to 0 and the result is
then proved by the reflexivity of equality.   


Proof of ∀ n', P n' → P (n'+1).

Suppose n' is an arbitrary natural number 
and we know that sum 0..n' = n'*(n'+1)/2.
In this context what remains to be shown is
sum 0..(n'+1)= P (n'+1) = (n'+1)((n'+1+1)/2.

Key observation: the sum of all the numbers
from 0 to n'+1 is the sum of all the numbers
from 0..n' + (n'+1) = (sum 0..n') + (n'+1). 
By assumption, this is n'(n'+1)/2 + (n'+1). 

The rest is just algebra. Writing (n'+1) as 
2(n'+1)/2, the sum is: (n'^2 + n'+2n' + 2)/2
= (n'^2 + 3n' + 2)/2. The numerator factors 
(n'+1)(n'+2) which we can then write as 
(n'+1)((n'+1)+1). We've thusproved P (n'+1): 
sum 0..(n'+1) = (n'+1)((n'+1)+1)/2, which is 
what we were to show. 

As we've already understood, our aim is to
show that from P n' (along with n') we can
derive P (n'+1). This generally requires us
to find a way to express P (n'+1) in terms
of P n'. That's what gives us a path from 
having a proof of P n' to obtaining a proof
of P (n'+1).

With proofs of P 0 and ∀ n', P n' → P (n'+1)
in hand, we can apply the induction principle
for natural numbers to finally prove that 
∀ n, P n. 

1. define and name property, here P
2. state theorem to prove, ∀ n, P n
3. construct a proof of (P 0)
4. construct a proof of ∀ n', P n' → P (n'+1)
5. apply induction to prove ∀ n, P n.

6. With this universal generalization proved
   you may now apply it to any value, n, to
   obtain a proof of P n'. Applying it in this
   way will recurse from n down to 0, build 
   the proof of P 0, then apply the induction
   hypothesis (also a univeral generalization)
   as many times as needed to construct the
   desired proof for n. What you've basically
   buil, by induction, is a machine/function
   that works recursively to construct a proof
   of P n for any given n, thus showing that
   there is a proof for any n, thus for all n.
-/