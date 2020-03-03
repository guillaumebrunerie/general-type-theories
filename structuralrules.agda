{-# OPTIONS --rewriting --prop #-}

open import common
open import syntx
open import derivability

{- Here are the structural rules, as derivation rules -}

module _ (Σ : Signature) where

{-

Γ ⊢ A    (x : A) ∈ Γ
--------------------
   Γ ⊢ x : A

-}

-- The version of the variable rule we use is that Γ ⊢ x : A if Γ ⊢ A holds, and if A is the type
-- corresponding to x in Γ.
VarRule : (k : ℕ) → DerivationRule Σ (([] , (0 , Ty)) , Tm)
rule (VarRule k) ↑ Γ ([] , ◇ ⊢ A) =
  do
    (k' , A') ← get k Γ
    assume (A' ≡ A)
    return (◇ ⊢ var k' :> A)

ConvRule : DerivationRule Σ (([] , (0 , Tm) , (0 , Ty=)) , Tm)
rule ConvRule ↑ Γ ([] , ◇ ⊢ u :> A , ◇ ⊢ A' == B) =
  do
    assume (A ≡ A')
    return (◇ ⊢ u :> B)

ConvEqRule : DerivationRule Σ (([] , (0 , Tm=) , (0 , Ty=)) , Tm=)
rule ConvEqRule ↑ Γ ([] , ◇ ⊢ u == v :> A , ◇ ⊢ A' == B) =
  do
    assume (A ≡ A')
    return (◇ ⊢ u == v :> B)

TyReflRule : DerivationRule Σ (([] , (0 , Ty)) , Ty=)
rule TyReflRule ↑ Γ ([] , ◇ ⊢ A) = return (◇ ⊢ A == A)

TySymmRule : DerivationRule Σ (([] , (0 , Ty=)) , Ty=)
rule TySymmRule ↑ Γ ([] , ◇ ⊢ A == B) = return (◇ ⊢ B == A)

TyTranRule : DerivationRule Σ (([] , (0 , Ty=) , (0 , Ty=)) , Ty=)
rule TyTranRule ↑ Γ ([] , ◇ ⊢ A == B , ◇ ⊢ B' == D) =  -- Can’t use C as a bound variable as it’s a tag.
  do
    assume (B ≡ B')
    return (◇ ⊢ A == D)


TmReflRule : DerivationRule Σ (([] , (0 , Tm)) , Tm=)
rule TmReflRule ↑ Γ ([] , ◇ ⊢ u :> A) = return (◇ ⊢ u == u :> A)

TmSymmRule : DerivationRule Σ (([] , (0 , Tm=)) , Tm=)
rule TmSymmRule ↑ Γ ([] , ◇ ⊢ u == v :> A) = return (◇ ⊢ v == u :> A)

TmTranRule : DerivationRule Σ (([] , (0 , Tm=) , (0 , Tm=)) , Tm=)
rule TmTranRule ↑ Γ ([] , ◇ ⊢ u == v :> A , ◇ ⊢ v' == w :> A') =
  do
    assume (v ≡ v')
    assume (A ≡ A')
    return (◇ ⊢ u == w :> A)

{-
Small hack to make our life easier, the implicit argument [ar] of [StructuralRulesType] is
automatically inferred from the definition of [StructuralRules], but for that they need to be
mutually recursive
-}

StructuralRules : DerivabilityStructure Σ

-- See #4366
private
  ar1 = _
  ar2 = _
  ar3 = _
  ar4 = _
  ar5 = _
  ar6 = _
  ar7 = _
  ar8 = _
  ar9 = _

data StructuralRulesType : {ar : JudgmentArity} → Set where
  var : ℕ → StructuralRulesType {ar1}
  conv : StructuralRulesType {ar2}
  convEq : StructuralRulesType {ar3}
  tyRefl : StructuralRulesType {ar4}
  tySymm : StructuralRulesType {ar5}
  tyTran : StructuralRulesType {ar6}
  tmRefl : StructuralRulesType {ar7}
  tmSymm : StructuralRulesType {ar8}
  tmTran : StructuralRulesType {ar9}

Rules StructuralRules S ar = StructuralRulesType {ar}
Rules StructuralRules T ar = Empty
Rules StructuralRules C ar = Empty
Rules StructuralRules Eq ar = Empty
derivationRule StructuralRules {t = S} (var k) = VarRule k
derivationRule StructuralRules {t = S} conv = ConvRule
derivationRule StructuralRules {t = S} convEq = ConvEqRule
derivationRule StructuralRules {t = S} tyRefl = TyReflRule
derivationRule StructuralRules {t = S} tySymm = TySymmRule
derivationRule StructuralRules {t = S} tyTran = TyTranRule
derivationRule StructuralRules {t = S} tmRefl = TmReflRule
derivationRule StructuralRules {t = S} tmSymm = TmSymmRule
derivationRule StructuralRules {t = S} tmTran = TmTranRule
