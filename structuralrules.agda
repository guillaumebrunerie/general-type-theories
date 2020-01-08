{-# OPTIONS --rewriting --prop #-}

open import common
open import syntx
open import derivability

{- Here are the structural rules, as [DerivationRule]s -}

module _ (Σ : Signature) where

  -- The version of the variable rule we use is that Γ ⊢ x : A if Γ ⊢ A holds, and if A is the type
  -- corresponding to x in Γ.
  VarRule : (k : ℕ) {n : ℕ} → DerivationRule Σ (([] , (0 , Ty)) , Tm) n
  rule (VarRule k) ↑ Γ ([] , ◇ ⊢ A) =
    do
      (k' , A') ← get k Γ
      assume (A' ≡ A)
      return (◇ ⊢ var k' :> A)

  ConvRule : {n : ℕ} → DerivationRule Σ (([] , (0 , Tm) , (0 , Ty=)) , Tm) n
  rule ConvRule ↑ Γ ([] , ◇ ⊢ u :> A , ◇ ⊢ A' == B) =
    do
      assume (A ≡ A')
      return (◇ ⊢ u :> B)

  ConvEqRule : {n : ℕ} → DerivationRule Σ (([] , (0 , Tm=) , (0 , Ty=)) , Tm=) n
  rule ConvEqRule ↑ Γ ([] , ◇ ⊢ u == v :> A , ◇ ⊢ A' == B) =
    do
      assume (A ≡ A')
      return (◇ ⊢ u == v :> B)

  TyReflRule : {n : ℕ} → DerivationRule Σ (([] , (0 , Ty)) , Ty=) n
  rule TyReflRule ↑ Γ ([] , ◇ ⊢ A) = return (◇ ⊢ A == A)

  TySymmRule : {n : ℕ} → DerivationRule Σ (([] , (0 , Ty=)) , Ty=) n
  rule TySymmRule ↑ Γ ([] , ◇ ⊢ A == B) = return (◇ ⊢ B == A)

  TyTranRule : {n : ℕ} → DerivationRule Σ (([] , (0 , Ty=) , (0 , Ty=)) , Ty=) n
  rule TyTranRule ↑ Γ ([] , ◇ ⊢ A == B , ◇ ⊢ B' == C) =
    do
      assume (B ≡ B')
      return (◇ ⊢ A == C)


  TmReflRule : {n : ℕ} → DerivationRule Σ (([] , (0 , Tm)) , Tm=) n
  rule TmReflRule ↑ Γ ([] , ◇ ⊢ u :> A) = return (◇ ⊢ u == u :> A)

  TmSymmRule : {n : ℕ} → DerivationRule Σ (([] , (0 , Tm=)) , Tm=) n
  rule TmSymmRule ↑ Γ ([] , ◇ ⊢ u == v :> A) = return (◇ ⊢ v == u :> A)

  TmTranRule : {n : ℕ} → DerivationRule Σ (([] , (0 , Tm=) , (0 , Tm=)) , Tm=) n
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

  data StructuralRulesType : {ar : JudgmentArity} → Set where
    var : ℕ → StructuralRulesType
    conv : StructuralRulesType
    convEq : StructuralRulesType
    tyRefl : StructuralRulesType
    tySymm : StructuralRulesType
    tyTran : StructuralRulesType
    tmRefl : StructuralRulesType
    tmSymm : StructuralRulesType
    tmTran : StructuralRulesType

  Rules StructuralRules ar = StructuralRulesType {ar}
  derivationRule StructuralRules (var k) = VarRule k
  derivationRule StructuralRules conv = ConvRule
  derivationRule StructuralRules convEq = ConvEqRule
  derivationRule StructuralRules tyRefl = TyReflRule
  derivationRule StructuralRules tySymm = TySymmRule
  derivationRule StructuralRules tyTran = TyTranRule
  derivationRule StructuralRules tmRefl = TmReflRule
  derivationRule StructuralRules tmSymm = TmSymmRule
  derivationRule StructuralRules tmTran = TmTranRule

