{-# OPTIONS --rewriting --prop #-}

open import common
open import common using (_===_)
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
  _,=_ : (t : TypeTheory) {ar : SyntaxArityArgs} {k : SyntaxSort} (r : EqualityRule (TTDer t) ar k) → TypeTheory

TTSig ◇ = Σ₀
TTSig (_,_ t {ar} r) = ExtSig (TTSig t) ar
TTSig (t ,= _) = TTSig t

TTDer ◇ = E₀
TTDer (t , r) = extend (TTDer t) (TRules r)
TTDer (t ,= r) = extendE (TTDer t) (ERule r)

{- Instances to make it possible to use numeric literals to refer to symbols and typing rules -}

instance
  NumΣ₀ : Number Empty
  Number.Constraint NumΣ₀ n = Empty

  NumExtSig : {A : SyntaxArity → Set} {ar ar' : SyntaxArity} {{_ : Number (A ar')}} → Number (ExtSigSymbols A ar ar')
  Number.Constraint (NumExtSig {ar = ar} {ar'}) zero = ar === ar'
  Number.Constraint (NumExtSig {{r}}) (suc n) = Number.Constraint r n
  Number.fromNat NumExtSig zero {{refl}} = new
  Number.fromNat (NumExtSig {{r}}) (suc n) = prev (Number.fromNat r n)

instance
  NumExtT : {A : JudgmentArity → Set} {ar : SyntaxArity} {ar' : JudgmentArity} {{_ : Number (A ar')}} → Number (ExtT A ar ar')
  Number.Constraint (NumExtT {ar = ar} {ar'}) zero = TArity ar === ar'
  Number.Constraint (NumExtT {{r}}) (suc n) = Number.Constraint r n
  Number.fromNat NumExtT zero {{refl}} = typingrule
  Number.fromNat (NumExtT {{r}}) (suc n) = prev (Number.fromNat r n)

  NumExtC : {A : JudgmentArity → Set} {ar : SyntaxArity} {ar' : JudgmentArity} {{_ : Number (A ar')}} → Number (ExtC A ar ar')
  Number.Constraint (NumExtC {ar = ar} {ar'}) zero = CArity ar === ar'
  Number.Constraint (NumExtC {{r}}) (suc n) = Number.Constraint r n
  Number.fromNat NumExtC zero {{refl}} = congruencerule
  Number.fromNat (NumExtC {{r}}) (suc n) = prev (Number.fromNat r n)

  NumExtE : {A : JudgmentArity → Set} {nar ar' : JudgmentArity} {{_ : Number (A ar')}} → Number (ExtE A nar ar')
  Number.Constraint (NumExtE {nar = nar} {ar'}) zero = nar === ar'
  Number.Constraint (NumExtE {{r}}) (suc n) = Number.Constraint r n
  Number.fromNat NumExtE zero {{refl}} = equalityrule
  Number.fromNat (NumExtE {{r}}) (suc n) = prev (Number.fromNat r n)
