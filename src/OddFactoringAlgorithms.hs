{-# LANGUAGE GADTs, TypeInType, ScopedTypeVariables,
             StandaloneDeriving, TypeFamilies, TypeOperators,
             AllowAmbiguousTypes, TypeApplications,
             UndecidableInstances, EmptyCase,
             FlexibleInstances, RankNTypes #-}

module OddFactoringAlgorithms where
import Library
import PrimeFac
import Unsafe.Coerce (unsafeCoerce)

import Data.Type.Equality

{- The onld one
factorOdd ::
  ( False ~ IsEven (Succ (Succ (Succ n)))
  , False ~ IsPrime (Succ (Succ (Succ n)))) =>
  SNat (Succ (Succ (Succ n))) ->
  SimpleFactoring (Succ (Succ (Succ n)))

factorOdd x@(SSucc r@(SSucc (SSucc (SSucc _)))) =
  dumbPf r &>>
  factorOddInternal Empty x r



factorOdd1 ::
  ( False ~ IsEven (Succ (Succ (Succ n)))
  , False ~ IsPrime (Succ (Succ (Succ n)))) =>
  SNat (Succ (Succ (Succ n))) ->
  SimpleFactoring (Succ (Succ (Succ n)))
-}

factorOdd ::
  ( False ~ IsEven (Succ (Succ (Succ n)))
  , False ~ IsPrime (Succ (Succ (Succ n)))) =>
  SNat (Succ (Succ (Succ n))) ->
  SimpleFactoring (Succ (Succ (Succ n)))

factorOdd x@(SSucc r@(SSucc (SSucc (SSucc _)))) =
  dumbPf r &>>
  factorOddInternal1 Empty x r



know1 :: forall n.
  SNat n ->
  True :~: (NotNatDivides (Succ (Succ (Succ n))) (Succ (Succ n)))
know1 SZero = Refl
know1 (SSucc n) =
  know1 n &>>
  lemma11 n &>>
  lemma12 n &>>
  Refl


lemma11 :: SNat n -> NatLT (Succ n) n :~: False
lemma11 SZero = Refl
lemma11 (SSucc n) = lemma11 n &>> Refl

lemma12 :: SNat n -> (Succ Zero) :~: ((Succ n) - n)
lemma12 SZero = Refl
lemma12 (SSucc n) = lemma12 n &>> Refl




factorOddInternal1 :: forall n d.
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

factorOddInternal1 _  (SSucc
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
factorOddInternal1 xs
                  n@(SSucc n')
                  d@(SSucc (d'@(SSucc d''))) =
  case sNatdivides d n of
    SFalse ->
      obviously d n &>>
      factorOddInternal1 (Cons Refl xs) n d'
    STrue ->
      multComm ndiv d'' &>>
      great n d &>>
      --great n ndiv &>>
      know1 d &>>
      know1 d' &>>
      know1 d'' &>>
      know1 ndiv &>>
      --rst d'' ndiv &>> -- what is t0 ???
      unsafeCoerce (SimpleFactoring (unsafeCoerce ndiv) d) where
        ndiv = truncatedDivision n d




droptwo :: SNat (Succ (Succ n)) -> SNat n
droptwo (SSucc (SSucc x)) = x


slen :: SNat n -> Nat
slen SZero = Zero
slen (SSucc x) = Succ $ slen x

-- n has type succ n
-- d has type succ d


















