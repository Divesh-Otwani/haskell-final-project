{-# LANGUAGE GADTs, TypeInType, ScopedTypeVariables,
             StandaloneDeriving, TypeFamilies, TypeOperators,
             AllowAmbiguousTypes, TypeApplications,
             UndecidableInstances, EmptyCase,
             FlexibleInstances, RankNTypes #-}

module PrimeFac where

import Library
import Data.Kind ( Type )
import Prelude hiding ()
import Data.Type.Equality
import GHC.TypeLits ( TypeError, ErrorMessage(..) )
import Unsafe.Coerce (unsafeCoerce) -- proofs are hard.

-- IsPrime and isPrime implementation:

type family NatDivides d n :: Bool where
  NatDivides Zero  _ = TypeError (Text "Divide by zero")
  NatDivides (Succ n) Zero = True
  NatDivides d n = If (NatLT n d) False (NatDivides d (n-d))

type family NotNatDivides n d where
  NotNatDivides n d = Not (NatDivides d n)

type family ImpDivisors n :: [Nat] where
  ImpDivisors Zero = TypeError (Text "No ImpDivisors")
  ImpDivisors (Succ Zero) = TypeError (Text "No ImpDivisors")
  ImpDivisors (Succ (Succ Zero)) = '[]
  ImpDivisors (Succ (Succ (Succ n)))
    = (Succ (Succ n)) ': ImpDivisors (Succ (Succ n))

type family IsPrime n :: Bool where
  IsPrime Zero = False
  IsPrime (Succ Zero) = False
  IsPrime (Succ (Succ n)) =
    IsPrimeInternal
      (Succ (Succ n))
      (ImpDivisors (Succ (Succ n)))

type family IsPrimeInternal (n :: Nat) (possDiv :: [Nat]) where
  IsPrimeInternal n '[] = True
  IsPrimeInternal n (x:xs) =
    And (NotNatDivides n x) (IsPrimeInternal n xs)

{-
Now, at the instance level.
-}

-- Only care about naturals >= 2
isPrime ::
  SNat (Succ (Succ n)) -> SBool (IsPrime (Succ (Succ n)))
isPrime m = isPrimeInternal m m


isPrimeInternal ::
  SNat (Succ (Succ n)) ->
  SNat (Succ (Succ m)) -> -- initially, m = n
  SBool (IsPrimeInternal
         (Succ (Succ n)) (ImpDivisors (Succ (Succ m))))
isPrimeInternal _ (SSucc (SSucc SZero)) = STrue
isPrimeInternal n (SSucc m@(SSucc (SSucc _))) =
  sAnd (notdivideSNat n m) (isPrimeInternal n m)


sNatdivides :: SNat d -> SNat n -> SBool (NatDivides d n)
sNatdivides SZero _ = error "Divide by zero"
sNatdivides (SSucc _) SZero = STrue
sNatdivides d@(SSucc _) n@(SSucc _) =
  case snatLT n d of
    STrue -> SFalse
    SFalse -> sNatdivides d (snatMinus n d)


sNot :: SBool b -> SBool (Not b)
sNot STrue = SFalse
sNot SFalse = STrue

sAnd :: SBool a -> SBool b -> SBool (And a b)
sAnd SFalse _ = SFalse
sAnd STrue SFalse = SFalse
sAnd STrue STrue = STrue

notdivideSNat ::
  SNat n -> SNat d -> SBool (Not (NatDivides d n))
notdivideSNat n d = sNot $ sNatdivides d n

-- Testing

toXSNat :: Int -> ExSNat
toXSNat n | n < 0 = error "lt 0"
          | n==0 = Ex SZero
          | otherwise = case toXSNat (n-1) of
              Ex sn -> Ex (SSucc sn)

isPrimetesting :: ExSNat -> Bool
isPrimetesting (Ex SZero) = False
isPrimetesting (Ex (SSucc SZero)) = False
isPrimetesting (Ex n@(SSucc (SSucc _))) =
  case isPrime n of
    STrue -> True
    SFalse -> False

isPrimetest :: Int -> Bool
isPrimetest = isPrimetesting . toXSNat

test = map (\x -> (x, isPrimetest x)) [1..100]


{-

And now, the good stuff.

-}

-- Note: really should combine the primality checking with
-- factoring because it is computationally faster

data PrimeFac :: Nat -> Type where
  SinglePrime :: (True ~ IsPrime n) => SNat n -> PrimeFac n
  PFacCompose :: PrimeFac n -> PrimeFac m -> PrimeFac (n*m)

instance Show (PrimeFac n) where
  show (SinglePrime p) = show (toInt p)
  show (PFacCompose p q) =
    show p ++ " * " ++ show q

data ExPFac where
  ExPFac :: PrimeFac a -> ExPFac

instance Show (ExPFac) where
  show (ExPFac pfac) = show pfac

data SimpleFactoring :: Nat -> Type where
  SimpleFactoring ::
    SNat (Succ (Succ m)) -> -- neither term can be 1
    SNat (Succ (Succ n)) ->
    SimpleFactoring ((Succ (Succ n))*(Succ (Succ m)))


primeFactors ::
  SNat (Succ (Succ n)) ->
  PrimeFac (Succ (Succ n))
primeFactors n@(SSucc (SSucc _)) = case isPrime n of
  STrue -> SinglePrime n
  SFalse -> case factor n of
    SimpleFactoring a b ->
      multComm a b &>>
      PFacCompose (primeFactors a) (primeFactors b)

pfactest :: Int -> ExPFac
pfactest x = case toXSNat x of
  Ex sn@(SSucc (SSucc _)) ->
    case primeFactors sn of
      pfac -> ExPFac pfac
  _ -> error "Too small int."

test_primefac_twoTooneTwenty =  map (\x -> (x, pfactest x)) [2..120]

factor :: -- factor numbers 4 or higher
  (False ~ IsPrime (Succ (Succ n))) =>
  SNat (Succ (Succ n)) ->
  SimpleFactoring (Succ (Succ n))

factor n@(SSucc (SSucc (SSucc (SSucc _)))) = case isEven n of
  STrue ->
    let
      two = (SSucc (SSucc SZero))
      tdiv = truncatedDivision n two
    in
      zero_right_identity tdiv &>>
      simRsuccDist tdiv &>>
      evenTruncComposition n &>>
      SimpleFactoring tdiv two
  SFalse -> factorOdd n



-- note: later, think about making the type neater
factorOdd ::
  ( False ~ IsEven (Succ (Succ (Succ n)))
  , False ~ IsPrime (Succ (Succ (Succ n)))) =>
  SNat (Succ (Succ (Succ n))) ->
  SimpleFactoring (Succ (Succ (Succ n)))

factorOdd x@(SSucc r@(SSucc (SSucc (SSucc _)))) =
  dumbPf r &>>
  factorOddInternal Empty x r


-- NotDivs l n
-- says that {l, l+1, ..., n -1} don't divide n
data NotDivs :: Nat -> Nat -> Type where
  Empty :: NotDivs (Succ n) (Succ n)
  Cons ::
    (False :~: NatDivides d n) ->
    NotDivs (Succ d) n ->
    NotDivs d n

data ExRefl where
  ExRefl :: (a :~: b) -> ExRefl

gatherInfo :: NotDivs a b -> ExRefl
gatherInfo Empty = ExRefl Refl
gatherInfo (Cons x@(Refl) xs) =
  case (gatherInfo xs) of
    ExRefl r@(Refl) -> ExRefl (x &*> r)



-- Later: skip re-checking the even factors
-- The code gets ugly here.

-- the number to factor is
   -- odd, composite and, greater than the
   -- check so far (which is m + 3)
   -- Also, (1 + check so far) ...  (n-1) are not

factorOddInternal :: forall n d.
  ( False ~ IsEven (Succ n)
  , False ~ IsPrime (Succ n)
  , True ~ (NatLT (Succ d) (Succ n))
  ) =>
  NotDivs (Succ (Succ d)) (Succ n) ->
  SNat (Succ n) ->
  SNat (Succ d) ->
  SimpleFactoring (Succ n)

-- my pattern matching is sufficient.
-- I just don't know (and don't want to)
-- prove to GHC that the smallest odd composite is 9

factorOddInternal _  (SSucc
                     (SSucc
                     (SSucc
                     (SSucc
                     (SSucc
                     (SSucc
                     (SSucc
                     (SSucc
                     (SSucc SZero)))))))))

                     (SSucc
                     (SSucc
                     (SSucc SZero))) =
                         SimpleFactoring three three where
                           three = SSucc (SSucc (SSucc SZero))

{-  The unsafe version

factorOddInternal xs
                  n@(SSucc _)
                  d@(SSucc (d'@(SSucc _))) =
  case sNatdivides d n of
    SFalse ->
      obviously d n &>>
      factorOddInternal (Cons Refl xs) n d'
    STrue ->
      case gatherInfo xs of
        ExRefl Refl -> -- this might be useless
          --great n d &>>
          unsafeCoerce
            (SimpleFactoring d (unsafeCoerce ndiv)) where
              ndiv = truncatedDivision n d


-}


-- Had to use unsafe coerce because the type was
-- too tricky to prove easily

factorOddInternal xs
                  n@(SSucc _)
                  d@(SSucc (d'@(SSucc _))) =
  case sNatdivides d n of
    SFalse ->
      obviously d n &>>
      factorOddInternal (Cons Refl xs) n d'
    STrue ->
      case gatherInfo xs of
        ExRefl Refl -> -- this might be useless
          --great n d &>>
          unsafeCoerce
            (SimpleFactoring d (unsafeCoerce ndiv)) where
              ndiv = truncatedDivision n d




obviously :: forall n d.
  (True ~ NatLT (Succ d) n) =>
  SNat (Succ d) ->
  SNat n ->
  True :~: NatLT d n

obviously (SSucc SZero) (SSucc (SSucc _)) = Refl
obviously d@(SSucc d'@(SSucc _)) (SSucc n'@(SSucc (SSucc _))) =
  obviously d' n' &>> Refl


dumb :: forall b a.
  (True ~ NatLT (Succ a) (Succ b)) =>
  True :~: NatLT a b
dumb = Refl


great :: forall n d.
  ( True ~ NatDivides (Succ d) (Succ n)) =>
  SNat (Succ n) ->
  SNat (Succ d) ->
  (Succ n) :~:
  ((TruncatedDiv
   (NatLT (Succ n) (Succ d))
   (Succ n)
   (Succ d)) * (Succ d))
great = error "testing"


-- first: do it on paper and reason carefully
-- then, try to type check it on paper


{- The base case is tricky

factorOddInternal _ n@(SSucc (SSucc (SSucc (SSucc (SSucc (SSucc _)))))) (SSucc (SSucc (SSucc SZero))) =
    zero_right_identity tdiv &>>
    SimpleFactoring tdiv three where
      three = SSucc (SSucc (SSucc SZero))
      tdiv = truncatedDivision n three



factorOddInternal
  xs
  n@(SSucc (SSucc (SSucc (SSucc (SSucc (SSucc _))))))
  d@(SSucc d'@(SSucc _)) =
    case sNatdivides d n of
      STrue -> SimpleFactoring d (truncatedDivision n d)
      SFalse -> factorOddInternal (Refl :> xs) n d'
-}


twoCantDivOdds :: forall n.
  ( False ~ IsEven n) =>
  SNat n ->
  False :~: (NatDivides (Succ (Succ Zero)) n)

twoCantDivOdds (SSucc SZero) = Refl
twoCantDivOdds n@(SSucc (SSucc n')) =
  decByTwoPresevesOddity n &>>
  twoCantDivOdds n' &>> Refl

decByTwoPresevesOddity ::
  (False ~ IsEven (Succ (Succ n))) =>
  SNat (Succ (Succ n)) ->
  False :~: IsEven n

decByTwoPresevesOddity n@(SSucc (SSucc n')) =
  notCancel (isEven n') &>> Refl

isEven :: SNat n -> SBool (IsEven n)
isEven SZero = STrue
isEven (SSucc n) = sNot $ isEven n

type family IsEven n where
  IsEven Zero = True
  IsEven (Succ n) = Not (IsEven n)


truncatedDivision ::
  SNat n ->
  SNat d ->
  SNat (TruncatedDiv (NatLT n d) n d)
truncatedDivision n d =
  case snatLT n d of
    STrue -> SZero
    SFalse -> (SSucc (truncatedDivision (snatMinus n d) d))

tdivAtleastOne ::
  (False ~ NatLT n (Succ d)) =>
  SNat n ->
  SNat (Succ d) ->
  SNat (Succ (TruncatedDiv (NatLT (n - (Succ d)) (Succ d)) (n - (Succ d)) (Succ d)))
tdivAtleastOne = truncatedDivision

-- I don't know how to express it,
-- but (b ~ NatLt n d)
type family TruncatedDiv (b :: Bool) (n:: Nat) (d :: Nat) where
  TruncatedDiv True n d  = Zero
  TruncatedDiv False n d =
    (Succ (TruncatedDiv (NatLT (n-d) d) (n-d) d))

evenTruncComposition ::
  (True ~ IsEven n) =>
  SNat n ->
  n :~: ((TruncatedDiv
          (NatLT n (Succ (Succ Zero)))
          n
          (Succ (Succ Zero))) +
        (TruncatedDiv
         (NatLT n (Succ (Succ Zero)))
         n
         (Succ (Succ Zero))))


evenTruncComposition SZero = Refl
evenTruncComposition (SSucc (SSucc n)) =
  notCancel (isEven n) &>>
  evenTruncComposition n &>>
  simRsuccDist n &>>
  simRsuccDist
    (truncatedDivision n
     (SSucc (SSucc SZero))) &>>
  Refl


notCancel :: SBool b -> (Not (Not b) :~: b)
notCancel STrue = Refl
notCancel SFalse = Refl

subtractPred ::
  SNat (Succ n) ->
  ((Succ n) - n) :~: (Succ Zero)
subtractPred (SSucc SZero) = Refl
subtractPred (SSucc x@(SSucc _)) =
  subtractPred x &>> Refl


dumbPf :: SNat n3 -> (True :~: (NatLT n3 (Succ n3)))
dumbPf SZero = Refl
dumbPf (SSucc n) = dumbPf n &>> Refl

dumbPf2 ::
  SNat n4 ->
  True :~: (NatLT n4 (Succ (Succ (Succ n4))))
dumbPf2 SZero = Refl
dumbPf2 (SSucc r) = dumbPf2 r &>> Refl


{-

Testing

-}


toInt :: SNat n -> Int
toInt SZero = 0
toInt (SSucc n) = 1 + (toInt n)










-- Scrap:



evalNotDivs :: NotDivs l n -> ExRefl
evalNotDivs Empty = ExRefl Refl
evalNotDivs (Cons Refl xs) =
  case evalNotDivs xs of
    ExRefl Refl -> ExRefl Refl



