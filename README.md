# HaskellFinalProj

The important stuff is 
- Library.hs
- PrimeFac.hs

In OddFactoringAlgorithms I messed around and got way closer
to proving it but didn't succeed. 

## What went well?

Expressing the types of primeFactors, factor, and 
making the GADTs for these things was fun and elegant.
Overall, I enjoyed the parts where I knew what I needed to prove
from a simple error message and went about proving it.

I hated reading long confusing error messages and guessing at a 
proof.


## What went poorly?

The type families and terrible design choices
that made some proofs near impossible.

I should use GADTs instead of type families to hold
constraints. Further, it isn't until now that I realized that
I could use type families to construct 
GADTs:

```haskell

data Prime :: Nat -> Type where
  Prime :: (IsPrime n :~: True) -> Prime n
    
 ```

## What should I have done?



Well, first of all, I should have understood that I need to
make my types, Gadt's and type families center around the 
major proofs, and NOT the other way around.

These are

1) Proving a number is prime
2) Proving a factoring is correct

Now, I would implement this function:

```haskell

factor :: 
  SNat (Succ n) -> 
  Either (Prime (Succ n)) (SimpleFactor (Succ n))

```
and create the type families to mirror this.



## New Stuff -- past the deadline

I am putting the new stuff is the folder, /better.





