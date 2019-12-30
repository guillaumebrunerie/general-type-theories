{-# OPTIONS --rewriting --prop #-}

open import Agda.Primitive public
open import Agda.Builtin.Nat public renaming (Nat to ℕ) hiding (_==_)
open import Agda.Builtin.List public
open import Agda.Builtin.Bool public


{- Cartesian product -}

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_ public

infixr 42 _×_
infixl 4 _,_


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

instance
  pairP : {A : Prop} {B : A → Prop} {{a : A}} {{b : B a}} → ΣP A B
  pairP {{a}} {{b}} = (a , b)

{- True -}

record ⊤ : Prop where
  instance constructor tt


{- False -}

data ⊥ : Prop where


{- Empty -}

data Empty : Set where


{- Unit -}

record Unit : Set where
  instance constructor tt


{- Natural numbers -}

record Number (A : Set) : Set₁ where
  field
    Constraint : ℕ → Set
    fromNat : (n : ℕ) {{_ : Constraint n}} → A

open Number {{...}} public

{-# BUILTIN FROMNAT fromNat #-}

instance
  NumNat : Number ℕ
  Number.Constraint NumNat _ = Unit
  Number.fromNat NumNat n = n


{- Equality -}

data _≡_ {l} {A : Set l} (x : A) : A → Prop l where
  instance refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REWRITE _≡_ #-}

infix 4 _≡_

ap : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
ap f refl = refl

_∙_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
refl ∙ refl = refl

infixr 4 _∙_

! : {A : Set} {a b : A} → a ≡ b → b ≡ a
! refl = refl


{- Lifting from Prop/Set to Set₁ -}

record Box (P : Prop) : Set where
  constructor box
  field
    unbox : P
open Box public


{- Finite sets -}

data VarPos : ℕ → Set where
  last : {n : ℕ} → VarPos (suc n)
  prev : {n : ℕ} → VarPos n → VarPos (suc n)

-- Size of the context before (and including) that variable
_-VarPos_ : (n : ℕ) → VarPos n → ℕ
n -VarPos k = suc (n -VarPos' k) where

  -- Size of the context before (and excluding) that variable
  _-VarPos'_ : (n : ℕ) → VarPos n → ℕ
  (suc m) -VarPos' last = m
  (suc m) -VarPos' prev k = m -VarPos' k

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

record Partial (A : Set) : Set₁ where
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

fail : {A : Set} → Partial A
isDefined fail = ⊥


{- Rewrite rules for the natural numbers (!) -}

+O-rewrite : {n : ℕ} → n + zero ≡ n
+O-rewrite {zero} = refl
+O-rewrite {suc n} = ap suc +O-rewrite
{-# REWRITE +O-rewrite #-}

+S-rewrite : {n m : ℕ} → m + suc n ≡ suc (m + n)
+S-rewrite {m = zero} = refl
+S-rewrite {m = suc m} = ap suc +S-rewrite
{-# REWRITE +S-rewrite #-}

assoc : {n m k : ℕ} → n + (m + k) ≡ (n + m) + k
assoc {n = zero} = refl
assoc {n = suc n} {m} {k} = ap suc (assoc {n = n} {m} {k})
{-# REWRITE assoc #-}


{- Properties of the natural numbers -}

data _≤_ : (n m : ℕ) → Prop where
  instance ≤0 : {n : ℕ} → 0 ≤ n
  ≤S : {n m : ℕ} → n ≤ m → suc n ≤ suc m

instance
  ≤r : {n : ℕ} → n ≤ n
  ≤r {zero} = ≤0
  ≤r {suc n} = ≤S ≤r

  ≤+ : {n m : ℕ} → n ≤ (m + n)
  ≤+ {zero} {m} = ≤0
  ≤+ {suc n} {m} = ≤S ≤+

  ≤tr : {n m k : ℕ} {{_ : n ≤ m}} {{_ : m ≤ k}} → n ≤ k
  ≤tr ⦃ ≤0 ⦄ ⦃ q ⦄ = ≤0
  ≤tr ⦃ ≤S p ⦄ ⦃ ≤S q ⦄ = ≤S (≤tr ⦃ p ⦄ ⦃ q ⦄)


{- Instance arguments -}

⟨⟩ : {A : Prop} {{a : A}} → A
⟨⟩ {{a}} = a


{- This is the sorts that we use for the syntax, two sorts: types and terms -}

data SyntaxSort : Set where
  Ty : SyntaxSort
  Tm : SyntaxSort


ap2 : {A B C : Set} (f : A → B → C) {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
ap2 f refl refl = refl

ap3 : {A B C D : Set} (f : A → B → C → D) {a a' : A} {b b' : B} {c c' : C} → a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
ap3 f refl refl refl = refl

ap4 : {A B C D E : Set} (f : A → B → C → D → E) {a a' : A} {b b' : B} {c c' : C} {d d' : D} → a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → f a b c d ≡ f a' b' c' d'
ap4 f refl refl refl refl = refl
