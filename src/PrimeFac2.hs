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






data PrimeFac :: Nat -> Type where
  SinglePrime :: (True ~ IsPrime n) => SNat n -> PrimeFac n
  PFacCompose :: PrimeFac n -> PrimeFac m -> PrimeFac (n*m)

data SimpleFactoring :: Nat -> Type where
  SimpleFactoring ::
    SNat (Succ (Succ m)) -> -- neither term can be 1
    SNat (Succ (Succ n)) ->
    SimpleFactoring ((Succ (Succ n))*(Succ (Succ m)))

data Prime :: Nat -> Type where
  Prime :: (IsPrime n :~: True) -> Prime n


factor ::
  SNat (Succ n) ->
  Either (Prime (Succ n)) (SimpleFactoring (Succ n))

factor = undefined

type family IsPrime where











instance Show (PrimeFac n) where
  show (SinglePrime p) = show (toInt p)
  show (PFacCompose p q) =
    show p ++ " * " ++ show q

