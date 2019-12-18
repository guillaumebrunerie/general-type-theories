{-# OPTIONS --rewriting --prop #-}

open import Agda.Primitive public
open import Agda.Builtin.Nat public renaming (Nat to ℕ) hiding (_==_)
open import Agda.Builtin.List public
open import Agda.Builtin.Bool public


{- Rewriting -}

postulate
  _↦_ : ∀ {l} {A : Set l} → A → A → Set l
{-# BUILTIN REWRITE _↦_ #-}


{- Cartesian product -}

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_ public

infixr 42 _×_
infixr 4 _,_


{- Σ-types -}

record ΣP (A : Prop) (B : A → Prop) : Prop where
  constructor _,_
  field
    fst : A
    snd : B fst
open ΣP public

record ΣS (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open ΣS public


{- True -}

record ⊤ : Prop where
  constructor tt


{- False -}

data ⊥ : Prop where


{- Equality -}

data _≡_ {l} {A : Set l} (x : A) : A → Prop l where
  instance refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

infix 4 _≡_

ap : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
ap f refl = refl

_∙_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
refl ∙ refl = refl

infixr 4 _∙_

! : {A : Set} {a b : A} → a ≡ b → b ≡ a
! refl = refl


{- Lifting from Prop/Set to Set₁ -}

record Box (P : Prop) : Set₁ where
  constructor box
  field
    unbox : P
open Box public

record Lift (A : Set) : Set₁ where
  constructor lift
  field
    unlift : A
open Lift public


{- Finite sets -}

data VarPos : ℕ → Set where
  last : {n : ℕ} → VarPos (suc n)
  prev : {n : ℕ} → VarPos n → VarPos (suc n)

data WeakPos : ℕ → Set where
  last : {n : ℕ} → WeakPos n
  prev : {n : ℕ} → WeakPos n → WeakPos (suc n)

weakenWeakPos : {n : ℕ} (m : ℕ) → WeakPos n → WeakPos (m + n)
weakenWeakPos zero k = k
weakenWeakPos (suc m) k = prev (weakenWeakPos m k)


{- Monads -}

record Monad {ℓ ℓ'} (M : Set ℓ → Set ℓ') : Set (lsuc ℓ ⊔ ℓ') where
  field
    return : {A : Set ℓ} → A → M A
    _>>=_ : {A B : Set ℓ} → M A → (A → M B) → M B

  _>>_ : {A B : Set ℓ} → M A → M B → M B
  a >> b = a >>= (λ _ → b)

  infixr 20 _>>_

open Monad {{…}} public


{- The partiality monad -}

record Partial (A : Set₁) : Set₁ where
  field
    isDefined : Prop
    _$_ : isDefined → A
  infix 5 _$_
open Partial public

instance
  PartialityMonad : Monad Partial
  isDefined (return {{ PartialityMonad }} x) = ⊤
  return {{ PartialityMonad }} x Partial.$ tt = x
  isDefined (_>>=_ {{ PartialityMonad }} a f) = ΣP (isDefined a) (λ x → isDefined (f (a $ x)))
  _>>=_ {{ PartialityMonad }} a f Partial.$ x = f (a $ fst x) $ snd x

assume : (P : Prop) → Partial (Box P)
isDefined (assume P) = P
unbox (assume P $ x) = x

fail : {A : Set₁} → Partial A
isDefined fail = ⊥


{- Rewrite rules for the natural numbers (!) -}

postulate
  +S-rewrite : {n m : ℕ} → (m + suc n) ↦ (suc (m + n))
  +O-rewrite : {n : ℕ} → (n + zero) ↦ n
  {-# REWRITE +S-rewrite #-}
  {-# REWRITE +O-rewrite #-}


{- Properties of the natural numbers -}

data _≤_ : (n m : ℕ) → Prop where
  instance ≤0 : {n : ℕ} → 0 ≤ n
  ≤S : {n m : ℕ} → n ≤ m → suc n ≤ suc m

instance
  ≤r : {n : ℕ} → n ≤ n
  ≤r {zero} = ≤0
  ≤r {suc n} = ≤S ≤r

instance
  ≤+ : {n m : ℕ} → n ≤ (m + n)
  ≤+ {zero} {m} = ≤0
  ≤+ {suc n} {m} = ≤S ≤+

instance
  ≤tr : {n m k : ℕ} {{_ : n ≤ m}} {{_ : m ≤ k}} → n ≤ k
  ≤tr ⦃ ≤0 ⦄ ⦃ q ⦄ = ≤0
  ≤tr ⦃ ≤S p ⦄ ⦃ ≤S q ⦄ = ≤S (≤tr ⦃ p ⦄ ⦃ q ⦄)


{- Instance arguments -}

⟨⟩ : {A : Prop} {{a : A}} → A
⟨⟩ {{a}} = a
