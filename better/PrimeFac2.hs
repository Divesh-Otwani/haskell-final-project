{-# LANGUAGE GADTs, TypeInType, ScopedTypeVariables,
             StandaloneDeriving, TypeFamilies, TypeOperators,
             AllowAmbiguousTypes, TypeApplications,
             UndecidableInstances, EmptyCase,
             FlexibleInstances, RankNTypes #-}

module PrimeFac2 where

import Library
import Data.Kind ( Type )
import Data.Type.Equality
import GHC.TypeLits ( TypeError, ErrorMessage(..) )
import Unsafe.Coerce (unsafeCoerce) -- proofs are hard.



{-

The interface.

-}


data PrimeFac :: Nat -> Type where
  SinglePrime :: Prime n -> PrimeFac n
  PFacCompose :: PrimeFac n -> PrimeFac m -> PrimeFac (n*m)

data SimpleFactoring :: Nat -> Type where
  SimpleFactoring ::
    SNat (Succ (Succ n)) -> -- neither term can be 1
    SNat (Succ (Succ m)) ->
    SimpleFactoring ((Succ (Succ n))*(Succ (Succ m)))

data Prime :: Nat -> Type where
  Prime ::
    SNat (Succ (Succ n)) ->   -- primes are >= 2
    IsPrime (Succ (Succ n)) :~: True ->
    Prime (Succ (Succ n))

primeFactorization ::
  SNat (Succ (Succ n)) ->
  PrimeFac (Succ (Succ n))

primeFactorization n@(SSucc (SSucc _)) = case factor n of
  Left p -> SinglePrime p
  Right (SimpleFactoring a b) ->
    PFacCompose (primeFactorization a) (primeFactorization b)



{-

Things to cleverly implement:

-}


type family IsPrime where

{-

Here the point is to implement IsPrime
and the type families it needs so that implementing
factor, below is as easy as possible.

The central proofs are

1) Show that if n | d, then d * (n // d) = n
   (Or (n // d) * d = n; I have a proof of commutivity.)

2) Show that if (for n > 2) {n-1, n-2, ..., 3, 2} all do not
divide n, then, True ~ IsPrime n.


-}


factor ::
  SNat (Succ n) ->
  Either (Prime (Succ n)) (SimpleFactoring (Succ n))

factor = undefined





