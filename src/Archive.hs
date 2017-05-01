{-# LANGUAGE GADTs, TypeInType, ScopedTypeVariables,
             StandaloneDeriving, TypeFamilies, TypeOperators,
             AllowAmbiguousTypes, TypeApplications,
             UndecidableInstances, EmptyCase,
             FlexibleInstances, RankNTypes #-}

module Archive where
import Library
-- first, untyped:

toNat :: Int -> Nat
toNat n | n < 0 = error "n < 0"
toNat 0 = Zero
toNat n = Succ (toNat $ n-1)

fromNat :: Nat -> Int
fromNat Zero = 0
fromNat (Succ n) = 1 + fromNat n

isprime :: Nat -> (Int, Bool)
isprime Zero = False
isprime (Succ Zero) = False
isprime n = (fromNat n, all (\d -> mod n d /= Zero ) $ possdivisors n)

mod :: Nat -> Nat -> Nat
mod n m = case subtract n m of
  Nothing -> n
  Just d -> mod d m

subtract :: Nat -> Nat -> Maybe Nat
subtract Zero     Zero      = Just Zero
subtract Zero     _        = Nothing
subtract n        Zero     = Just n
subtract (Succ n) (Succ m) = subtract n m

possdivisors :: Nat -> [Nat] -- {2, 3, ..., n-1}
possdivisors Zero = error "Zero has no poss. divisors"
possdivisors (Succ Zero) = error "One has no poss. divisors"
possdivisors (Succ (Succ Zero)) = []
possdivisors (Succ n@(Succ (Succ _))) = n : possdivisors n

-- Now, the primality checker at the type level
{-
type family IsPrime n where
  IsPrime Zero = False
  IsPrime (Succ Zero) = False
  IsPrime n = all (\d -> mod n d /= Zero) (PossDivsors n)
-}

type family PossDivsors (n:: Nat) :: [Nat] where
  PossDivsors Zero = '[]
  PossDivsors (Succ Zero) = '[]
  PossDivsors (Succ (Succ Zero)) = '[]
  PossDivsors (Succ (Succ (Succ m)))
    = (Succ (Succ m)) : (PossDivsors (Succ (Succ m)))







-- untyped list of all primes as ints

nextprime :: [Int] -> Int ->  Int
nextprime primes start
  | all (\m -> mod start m /= 0) primes = start
  | otherwise                           = nextprime primes (start + 1)






type family AllNat (f :: Nat -> Bool) (ns :: [Nat]) :: Bool where
  AllNat f '[] = 'True
  AllNat f (x ': xs) = If (f x) (AllNat f xs) 'False


type family ModNat n d where
  ModNat n Zero = TypeError (Text "Can't divide by zero.")
  ModNat n (Succ m) =
    If (NatLT n (Succ m)) n (ModNat (n - (Succ m)) (Succ m))
    -- Darn. I need a proof ^ there to show
    -- that eventually the first argument is less than
    -- the second.

type family NatDivides n d :: Bool where
  NatDivides n d = NatEq (ModNat n d) Zero


impDivisors ::
  SNat (Succ (Succ n)) -> [ExSNat] -- there exists a solution
--impDivisors SZero = error "no impDivisors"
--impDivisors (SSucc SZero) = error "no impDivisors"
impDivisors (SSucc (SSucc SZero)) = []
impDivisors (SSucc a@(SSucc (SSucc _))) = (Ex a) : impDivisors a



{-
modSNat :: SNat n -> SNat m -> SNat (ModNat n m)
modSNat _ SZero = error "Can't divide by zero"
modSNat n m@(SSucc _) =
  if (snatLT n m == STrue)
  then n
  else modSNat (snatMinus n m) m

-}




{-
isPrimeInternal ::
  SNat (Succ (Succ m)) ->
  SNat (Succ (Succ m)) ->
  SBool (IsPrimeInternal (Succ (Succ m)) (ImpDivisors (Succ (Succ m))))
isPrimeInternal n m = ippi n m
-}

-- screw the types here
maybeDivide :: SNat n -> SNat (Succ d) -> Maybe ExSNat

maybeDivide SZero _ = Just $ Ex SZero
maybeDivide n@(SSucc _) d = case snatLT n d of
  STrue -> Nothing
  SFalse ->
    do
      Ex recur <- maybeDivide (snatMinus n d) d
      return $ Ex $ SSucc recur





{-



factor ::
  (False ~ IsPrime (Succ (Succ n))) =>
  SNat (Succ (Succ n)) ->
  (  (a * (Succ (Succ b))) ~ (Succ (Succ n))  =>
    (SNat a, SNat (Succ (Succ b)))  )

factor n = case isEven n of
  STrue -> (truncatedDivision n two, two) where
    two :: SNat (Succ (Succ Zero))
    two = SSucc (SSucc SZero)
-- incomplete cases



factorEven ::
  (IsEven n ~ True) =>
  SNat n ->
  ( SNat (Succ (Succ Zero))
  , SNat (TruncatedDiv (NatLT n (Succ (Succ Zero))) n (Succ (Succ Zero))))

factorEven n = (two, truncatedDivision n two) where
  two = SSucc (SSucc SZero)
-}




oddNumFacs :: forall (d::Nat) n.
  ( False ~ IsEven n
  , True  ~ IsEven (Succ d)
  ) =>
  SNat (Succ d) ->
  SNat n ->
  False :~: (NatDivides (Succ d) n)
{-
oddNumFacs (SSucc (SSucc SZero)) n =
  twoCantDivOdds n &>>
  Refl
-}
oddNumFacs d@(SSucc _) (n@(SSucc _) :: SNat x) =
  case snatLT n d of
    STrue -> Refl
    SFalse ->
      oddMinusEvenisOdd @x d &>>
      case oddNumFacs d (snatMinus n d) of
        Refl -> Refl

oddMinusEvenisOdd :: forall n d.
  ( False ~ IsEven n
  , True ~ IsEven d
  --, False ~ NatLT n d
  ) =>
  SNat d ->
  False :~: (IsEven (n-d))
oddMinusEvenisOdd SZero = Refl
oddMinusEvenisOdd d@(SSucc (SSucc d')) =
  notCancel (isEven d') &>>
  notCancel (isEven d) &>>
  oddMinusEvenisOdd @n d' &>>
  Refl
{-
ltTrans :: forall n d.
  ( False ~ NatLT n (Succ (Succ d))) =>
  SNat (Succ (Succ d)) ->
  False :~: NatLT n d
ltTrans (SSucc (SSucc SZero)) = Refl
ltTrans d@(SSucc (SSucc d'@(SSucc (SSucc _)))) =
  ltTrans @n d' &>> Refl

-}





