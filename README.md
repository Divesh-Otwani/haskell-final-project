# HaskellFinalProj

## Description

For my final project, I tried to implement a formally verified prime factorization algorithm.
The whole point of this is to demonstrate non-trivial verification.
Usually, formal verification in haskell ends up being "do exactly what you do at the instance level at the type level." This doesn't really show formal verification. The idea here is to solve and formally verify your solution of a problem for which the algorithm is distinct from the type level stuff. 


I didn't succeed and needed to use unsafeCoerce at one critical point.
However, I learned a lot about good design and GADT + type familily + constraint usage for verification.

The key function is at line 141 in src/PrimeFac.hs: `primeFactors`.

## unsafeCoerce

I used unsafeCoerce to argue that n | m  implies n * (m // n) = m
for n>3. I proved this for n=2 but had enourmous difficulty generalizing that proof.


## Directories

The important stuff is 
- src/Library.hs
- src/PrimeFac.hs

(In OddFactoringAlgorithms I messed around and got way closer to avoiding unsafeCoerce.)

## What went well?

Expressing the types of primeFactors, factor, and 
making the GADTs for these things was fun and elegant.
Overall, I enjoyed the parts where I knew what I needed to prove
from a simple error message and went about proving it.

I hated reading long confusing error messages and guessing at a 
proof.


## What went poorly? What did I learn?

The type families and terrible design choices
that made some proofs incredibly hard and annoying.

I should use GADTs instead of type families to hold
constraints. 
Further, it isn't until now that I realized that
I could use type families to construct nice
GADTs:

```haskell

data Prime :: Nat -> Type where
  Prime :: (IsPrime n :~: True) -> Prime n
    
 ```

The key observation is the following.

> Use the *structure* of types instead of type families to encode correctness properties. For example, make GADTS for the "return types" of functions such that they express correctness properties. Look at my PrimeFac type on line 119 in src/PrimeFac.hs. This was the start of a good idea.


## Concretely, What should I have done?


Well, first of all, I should have understood that I need to
make my types, Gadt's and type families center around the 
major proofs, and NOT the other way around. In this way, the structure of types helps prove and encode correctness properties.

The key proofs are

* Proving a number is prime
(This proof is one I have accomplished. It's just important to note that it could be done better.)
* Proving a factoring is correct

Now, I would implement this function:

```haskell

factor :: 
  SNat (Succ n) -> 
  Either (Prime (Succ n)) (SimpleFactor (Succ n))

```
and create the GADTS and type families to help prove this.

These ideas are written in an interface in /better.






