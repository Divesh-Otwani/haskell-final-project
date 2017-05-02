{-# LANGUAGE GADTs, TypeInType, ScopedTypeVariables,
             StandaloneDeriving, TypeFamilies, TypeOperators,
             AllowAmbiguousTypes, TypeApplications,
             UndecidableInstances, EmptyCase,
             RankNTypes #-}

module Library where

import Data.Kind ( Type )
import GHC.TypeLits ( TypeError, ErrorMessage(..) )
import Data.Type.Equality
import Prelude hiding ( (*) )

(&>>) :: (a :~: b) -> (a ~ b => c) -> c
Refl &>> x = x
infixr 5 &>>

-- taken from class
data Ex :: (k -> Type) -> Type where
  Ex :: forall (t :: k -> Type) (x :: k). t x -> Ex t

type ExSNat = Ex SNat


data SBool :: Bool -> Type where
  STrue :: SBool True
  SFalse :: SBool False

deriving instance Show (SBool b)
deriving instance Eq (SBool b)


data Nat where
  Zero :: Nat
  Succ :: Nat -> Nat
  deriving (Show, Eq)


data SNat :: Nat -> Type where
  SZero :: SNat Zero
  SSucc :: SNat n -> SNat (Succ n)
deriving instance Show (SNat n)


type family (a :: Nat) * (b :: Nat) :: Nat where
  Zero   * b = Zero
  Succ a * b = b + (a * b)
infixl 7 *


type family If cond (this :: a) (orthat :: a) where
  If 'True this orthat = this
  If 'False this orthat = orthat

-- maybe one day try and implement generic type equality

type family Not b where
  Not True = False
  Not False = True

type family NatEq n m where
  NatEq Zero Zero = True
  NatEq Zero _ = False
  NatEq _ Zero = False
  NatEq (Succ n) (Succ m) = NatEq n m

type family NotNatEq n m where
  NotNatEq n m = Not (NatEq n m)


type family NatLT (n :: Nat) (m :: Nat) :: Bool where
  NatLT _         Zero    = False
  NatLT Zero      (Succ m)       = True
  NatLT (Succ n) (Succ m) = NatLT n m

snatLT :: SNat n -> SNat m -> SBool (NatLT n m)
snatLT _         SZero     = SFalse
snatLT SZero     (SSucc _) = STrue
snatLT (SSucc n) (SSucc m) = snatLT n m


type family (a :: Nat) - (b :: Nat) :: Nat where
  b - Zero            = b
  Zero - a            = TypeError (Text "Bad subtraction")
  (Succ n) - (Succ m) = n - m
infixl 6 -


snatMinus :: SNat n -> SNat m -> SNat (n-m)
snatMinus x SZero = x
snatMinus SZero _ = error "Bad minus"
snatMinus (SSucc n) (SSucc m) = snatMinus n m


type family (a :: Nat) + (b :: Nat) :: Nat where
  Zero   + b = b
  Succ a + b = Succ (a + b)
infixl 6 +

snatPlus :: SNat n -> SNat m -> SNat (n+m)
snatPlus SZero x = x
snatPlus (SSucc n) x = SSucc $ snatPlus n x

type family And a b where
  And False _ = False
  And _ False = False
  And True True = True


{-

Proofs on lots of things.

-}


simRsuccDist :: SNat n -> (n + Succ n) :~: Succ (n + n)
simRsuccDist (n :: SNat m) = right_succ_distributivity @m n

right_succ_distributivity :: forall m' n.
  SNat n -> (n + 'Succ m') :~: 'Succ (n + m')
right_succ_distributivity SZero      = Refl
right_succ_distributivity (SSucc n') =
  case right_succ_distributivity @m' n' of Refl -> Refl

rst :: SNat n -> SNat (Succ m) -> (n + Succ m) :~: Succ (n + m)
rst n (SSucc (_ :: SNat m1)) = right_succ_distributivity @m1 n


zero_right_identity :: SNat n -> (n + 'Zero :~: n)
zero_right_identity SZero     = Refl
zero_right_identity (SSucc n) =
  case zero_right_identity n of Refl -> Refl


plusComm :: forall (a::Nat) (b::Nat).
  SNat a -> SNat b -> a + b :~: b + a
plusComm SZero                    b =
  zero_right_identity b &>> Refl
plusComm (SSucc (a' :: SNat na')) b =
  plusComm a' b
  &>> right_succ_distributivity @na' b
  &>> Refl


plusAssoc :: forall a b c.
  SNat a -> (a + b) + c :~: a + (b + c)
plusAssoc SZero = Refl
plusAssoc (SSucc a') = plusAssoc @_ @b @c a' &>> Refl


--------------------------------------------------------------
------- Proofs on Multiplication
--------------------------------------------------------------


multComm :: forall a b. SNat a -> SNat b-> a * b :~: b * a
multComm SZero  b = case rightZeroMult b of Refl -> Refl
multComm (SSucc a') b = pf &>> Refl where
  pf = multComm a' b &*> lemma1 a' b


-- This pcons thing below was prof E
pcons :: (a :~: b) -> (c :~: d) -> ('(a,c) :~: '(b,d))
pcons Refl Refl = Refl

(&*>) = pcons
infixr 5 &*>

rightZeroMult :: SNat b -> (b * Zero) :~: Zero
rightZeroMult SZero      = Refl
rightZeroMult (SSucc b') = rightZeroMult b' &>> Refl


lemma1 :: forall a' b.
  SNat a' -> SNat b -> b + (b * a') :~: b * (Succ a')
lemma1  _ SZero = Refl
lemma1 (a' :: SNat ta') (SSucc (b' :: SNat tb') :: SNat tb) =
  plusAssoc @_ @a' @(tb'*a') b'
  &>> plusComm b' a'
  &>> plusAssoc @_ @tb' @(tb'*ta') a'
  &>> lemma1 a' b'
  &>> Refl



