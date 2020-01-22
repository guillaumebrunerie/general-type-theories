{-# OPTIONS --rewriting --prop #-}

open import Agda.Primitive public
open import Agda.Builtin.Nat public renaming (Nat to ℕ) hiding (_==_; _+_)
open import Agda.Builtin.Bool public

{- Basic datatypes and propositions -}

record ⊤ : Prop where
  instance constructor tt

record Unit : Set where
  instance constructor tt

data ⊥ : Prop where

data Empty : Set where

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_ public

infixr 42 _×_
infixl 4 _,_

record ΣP (A : Prop) (B : A → Prop) : Prop where
  constructor _,_
  field
    fst : A
    snd : B fst
open ΣP public

instance
  pairP : {A : Prop} {B : A → Prop} {{a : A}} {{b : B a}} → ΣP A B
  pairP {{a}} {{b}} = a , b

record ΣS (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open ΣS public


{-
Literal notation for natural numbers and similar things.
Later on we will use notation with literal natural numbers for things that are not always defined,
so we need to use [fromNat] and a constraint. The idea is that if we have an instance of
[Number A], that means that we can potentially use literals to denote elements of [A], as long as
instance search can figure out that the constraint is satisfied.
We need the constraint to be a set as we will pattern match on it.
-}

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
--{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REWRITE _≡_ #-}

infix 4 _≡_

ap : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
ap f refl = refl

ap2 : {A B C : Set} (f : A → B → C) {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
ap2 f refl refl = refl

ap3 : {A B C D : Set} (f : A → B → C → D) {a a' : A} {b b' : B} {c c' : C} → a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
ap3 f refl refl refl = refl

ap4 : {A B C D E : Set} (f : A → B → C → D → E) {a a' : A} {b b' : B} {c c' : C} {d d' : D} → a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → f a b c d ≡ f a' b' c' d'
ap4 f refl refl refl refl = refl

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


{- Monads -}

record Monad {ℓ ℓ'} (M : Set ℓ → Set ℓ') : Set (lsuc ℓ ⊔ ℓ') where
  field
    return : {A : Set ℓ} → A → M A
    _>>=_ : {A B : Set ℓ} → M A → (A → M B) → M B

  _>>_ : {A B : Set ℓ} → M A → M B → M B
  a >> b = a >>= (λ _ → b)

  infixr 20 _>>_

open Monad {{…}} public


{- For the partiality monad, we use (dependent) lists of propositions in order to get rid of useless ⊤s -}

data ListProp : Set₁
pf : ListProp → Prop

data ListProp where
  [] : ListProp
  [_] : Prop → ListProp
  _,_ : (l : ListProp) → (pf l → ListProp) → ListProp

pf [] = ⊤
pf [ p ] = p
pf ([] , p) = pf (p tt)
pf (l , q) = ΣP (pf l) (λ x → pf (q x))

lemma : {l : ListProp} {p : pf l → ListProp} → pf (l , p) → ΣP (pf l) (λ x → pf (p x))

lemma {[]} q = tt , q
lemma {[ p ]} q = q
lemma {l , p} {r} q = (fst q , snd q)

{- The partiality monad -}

record Partial (A : Set) : Set₁ where
  field
    listIsDefined : ListProp
    _$_ : pf listIsDefined → A
  infix 5 _$_
open Partial public

isDefined : {A : Set} → Partial A → Prop
isDefined P = pf (listIsDefined P)

instance
  PartialityMonad : Monad Partial
  listIsDefined (Monad.return PartialityMonad x) = []
  Monad.return PartialityMonad x Partial.$ tt = x
  listIsDefined (Monad._>>=_ PartialityMonad a f) = listIsDefined a , (λ x → listIsDefined (f (a $ x)))
  Monad._>>=_ PartialityMonad a f Partial.$ x = let x' = lemma {listIsDefined a} x in f (a $ fst x') $ snd x'

assume : (P : Prop) → Partial (Box P)
listIsDefined (assume P) = [ P ]
assume P $ x = box x

fail : {A : Set} → Partial A
listIsDefined fail = [ ⊥ ]


{- Properties of the natural numbers -}

data _≤_ : (n m : ℕ) → Set where
  instance ≤r : {n : ℕ} → n ≤ n
  ≤S : {n m : ℕ} → n ≤ m → n ≤ suc m

≤P : {n m : ℕ} → suc n ≤ suc m → n ≤ m
≤P ≤r = ≤r
≤P {n} {suc m} (≤S p) = ≤S (≤P p)

_+_ : ℕ → ℕ → ℕ
n + zero = n
n + suc m = suc (n + m)

instance
  ≤-+ : {n m : ℕ} → n ≤ (n + m)
  ≤-+ {m = zero} = ≤r
  ≤-+ {m = suc m} = ≤S (≤-+ {m = m})

instance
  ≤S0 : {n : ℕ} → n ≤ suc n
  ≤S0 = ≤S ≤r

  0≤ : {n : ℕ} → 0 ≤ n
  0≤ {zero} = ≤r
  0≤ {suc n} = ≤S (0≤ {n})

≤SS : {n m : ℕ} {{_ : n ≤ m}} → suc n ≤ suc m
≤SS {.0} {zero} ⦃ ≤r ⦄ = ≤r
≤SS {.(suc m)} {suc m} ⦃ ≤r ⦄ = ≤r
≤SS {n} {suc m} ⦃ ≤S p ⦄ = ≤S (≤SS {n} {m} {{p}})

≤+ : (l : ℕ) {n m : ℕ} {{_ : n ≤ m}} → (n + l) ≤ (m + l)
≤+ l {{≤r}} = ≤r
≤+ zero {{ ≤S p }} = ≤S p
≤+ (suc l) {{ ≤S p }} = ≤SS {{≤+ l {{≤S p}}}}
-- ≤+ zero {{p}} = p
-- ≤+ (suc l) = ≤SS {{≤+ l}}

≤tr : {n m k : ℕ} {{_ : n ≤ m}} {{_ : m ≤ k}} → n ≤ k
≤tr ⦃ ≤r ⦄ ⦃ q ⦄ = q
≤tr ⦃ ≤S p ⦄ ⦃ ≤r ⦄ = ≤S p
≤tr ⦃ ≤S p ⦄ ⦃ ≤S q ⦄ = ≤S (≤tr {{≤S p}} {{q}})


{- Rewrite rules for the natural numbers (!!!) -}

-- +O-rewrite : {n : ℕ} → n + zero ≡ n
-- +O-rewrite {zero} = refl
-- +O-rewrite {suc n} = ap suc +O-rewrite
-- {-# REWRITE +O-rewrite #-}

-- +S-rewrite : {n m : ℕ} → m + suc n ≡ suc (m + n)
-- +S-rewrite {m = zero} = refl
-- +S-rewrite {m = suc m} = ap suc +S-rewrite
-- {-# REWRITE +S-rewrite #-}

data _===_ {l} {A : Set l} (x : A) : A → Set l where
  instance refl : x === x
{-# BUILTIN EQUALITY _===_ #-}

infix 4 _===_

assoc : {n m k : ℕ} → (n + m) + k ≡ n + (m + k)
assoc {k = zero} = refl
assoc {n} {m} {k = suc k} = ap suc (assoc {n} {m} {k = k})
--{-# REWRITE assoc #-}

transport : {A : Set} {P : A → Set} {a b : A} → a === b → P a → P b
transport refl u = u

transport! : {A : Set} {P : A → Set} {a b : A} → a === b → P b → P a
transport! refl u = u


{- Instance arguments -}

⟨⟩ : {A : Prop} {{a : A}} → A
⟨⟩ {{a}} = a


{- This is the sorts that we use for the syntax, two sorts: types and terms -}

data SyntaxSort : Set where
  Ty : SyntaxSort
  Tm : SyntaxSort


{- Positions of variables in a context -}

data VarPos : ℕ → Set where
  last : {n : ℕ} → VarPos (suc n)
  prev : {n : ℕ} → VarPos n → VarPos (suc n)

-- Size of the context before (and excluding) that variable
_-VarPos'_ : (n : ℕ) → VarPos n → ℕ
(suc n) -VarPos' last = n
(suc n) -VarPos' prev k = n -VarPos' k

-- Size of the context before (and including) that variable
_-VarPos_ : (n : ℕ) → VarPos n → ℕ
n -VarPos k = suc (n -VarPos' k)

--instance
suc-VarPos'≤ : {n : ℕ} {p : VarPos (suc n)} → (suc n -VarPos' p) ≤ n
suc-VarPos'≤ {n} {last} = ≤r
suc-VarPos'≤ {suc n} {prev p} = ≤tr {{suc-VarPos'≤ {n} {p}}} {{≤S ≤r}}


{- Positions of weakening spots in a context -}

data WeakPos : ℕ → Set where
  last : {n : ℕ} → WeakPos n
  prev : {n : ℕ} → WeakPos n → WeakPos (suc n)

-- weakPosAt : {m : ℕ} (n : ℕ) → WeakPos (m + n)
-- weakPosAt zero = last
-- weakPosAt (suc n) = prev (weakPosAt n)

-- weakenWeakPos : {n : ℕ} (m : ℕ) → WeakPos n → WeakPos (n + m)
-- weakenWeakPos zero k = k
-- weakenWeakPos (suc m) k = prev (weakenWeakPos m k)

weakenWeakPos2 : {n m : ℕ} {{_ : n ≤ m}} → WeakPos n → WeakPos m
weakenWeakPos2 ⦃ ≤r ⦄ k = k
weakenWeakPos2 ⦃ ≤S p ⦄ k = prev (weakenWeakPos2 {{p}} k)
