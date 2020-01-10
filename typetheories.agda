{-# OPTIONS --rewriting --prop #-}

open import common
open import syntx
open import derivability
open import structuralrules
open import typingrules


{- Type theories -}

Σ₀ : Signature
Symbols Σ₀ ar = Empty

E₀ : DerivabilityStructure Σ₀
E₀ = StructuralRules Σ₀


data TypeTheory : Set
TTSig : TypeTheory → Signature
TTDer : (t : TypeTheory) → DerivabilityStructure (TTSig t)

data TypeTheory where
  ◇ : TypeTheory
  _,_ : (t : TypeTheory) {ar : SyntaxArity} (r : TypingRule (TTDer t) (args ar) (sort ar)) → TypeTheory
  _,=_ : (t : TypeTheory) {ar : SyntaxArityArgs} {k : JudgmentSort} (r : EqualityRule (TTDer t) ar k) → TypeTheory

TTSig ◇ = Σ₀
TTSig (_,_ t {ar} r) = ExtSig (TTSig t) ar
TTSig (t ,= _) = TTSig t

TTDer ◇ = E₀
TTDer (t , r) = extend (TTDer t) (TRules r)
TTDer (t ,= r) = extend0 (TTDer t) (ERule _ r)


{- Instances to make it possible to use numeric literals to refer to symbols and typing rules -}

data _===_ {l} {A : Set l} (x : A) : A → Set l where
  instance refl : x === x

instance
  NumΣ₀ : Number Empty
  Number.Constraint NumΣ₀ n = Empty

  NumExtSig : {A : SyntaxArity → Set} {ar ar' : SyntaxArity} {{_ : Number (A ar')}} → Number (ExtSigSymbols A ar ar')
  Number.Constraint (NumExtSig {ar = ar} {ar'}) zero = ar === ar'
  Number.Constraint (NumExtSig {{r}}) (suc n) = Number.Constraint r n
  Number.fromNat NumExtSig zero {{refl}} = new
  Number.fromNat (NumExtSig {{r}}) (suc n) = prev (Number.fromNat r n)

  NumStructuralRulesType : {Σ : Signature} {ar : JudgmentArity} → Number (StructuralRulesType Σ {ar})
  Number.Constraint NumStructuralRulesType n = Empty

  NumExt : {A : JudgmentArity → Set} {ar : SyntaxArity} {ar' : JudgmentArity} {{_ : Number (A ar')}} → Number (Ext A ar ar')
  Number.Constraint (NumExt {ar = ar} {ar'}) zero = TArity ar === ar'
  Number.Constraint (NumExt {{r}}) (suc n) = Number.Constraint r n
  Number.fromNat NumExt zero {{refl}} = typingrule
  Number.fromNat (NumExt {{r}}) (suc n) = prev (Number.fromNat r n)

  NumExt0 : {A : JudgmentArity → Set} {nar ar' : JudgmentArity} {{_ : Number (A ar')}} → Number (Ext0 A nar ar')
  Number.Constraint (NumExt0 {nar = nar} {ar'}) zero = nar === ar'
  Number.Constraint (NumExt0 {{r}}) (suc n) = Number.Constraint r n
  Number.fromNat NumExt0 zero {{refl}} = equalityrule
  Number.fromNat (NumExt0 {{r}}) (suc n) = prev (Number.fromNat r n)


record HasStructuralRules (Σ : Signature) (A : JudgmentArity → Set) : Set where
  field
    str : {ar : JudgmentArity} → StructuralRulesType Σ {ar = ar} → A ar
open HasStructuralRules {{...}} public

instance
  HasStructuralRules-id : {Σ : Signature} → HasStructuralRules Σ (λ ar → StructuralRulesType Σ {ar})
  HasStructuralRules.str HasStructuralRules-id x = x

  HasStructuralRules-Ext : {Σ : Signature} {A : JudgmentArity → Set} {ar : SyntaxArity}
                           {{_ : HasStructuralRules Σ A}} → HasStructuralRules Σ (Ext A ar)
  HasStructuralRules.str HasStructuralRules-Ext x = prev (str x)
