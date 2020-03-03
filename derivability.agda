{-# OPTIONS --rewriting --prop #-}

open import common
open import syntx

{- The sort corresponding to judgments -}

data JudgmentSort : Set where
  Ty  : JudgmentSort
  Tm  : JudgmentSort
  Ty= : JudgmentSort
  Tm= : JudgmentSort

JudgmentArityArgs = ArityArgs JudgmentSort
JudgmentArity = Arity JudgmentSort

{-
Judgments are indexed by the signature, their ambient context, the length of their local context,
and their sort.

We can see judgments as consisting of two contexts, one normal context (the ambient context) and
then one dependent context (the local context). The reason is that all typing rules occur in an
ambient context which never changes, and sometimes add new assumptions (to the local context).
Therefore we will never have to check that the ambient contexts are equal, it will be forced by the
typing.

Indexing judgments by sorts is very good to get rid of absurd cases, when giving typing rules and
that some judgments are supposed to have certain sorts.
-}

data Judgment (Σ : Signature) {m : ℕ} (Γ : Ctx Σ m) (n : ℕ) : JudgmentSort → Set where
  _⊢_       : (Δ : DepCtx Σ m n) → TyExpr Σ (m + n) → Judgment Σ Γ n Ty
  _⊢_:>_    : (Δ : DepCtx Σ m n) → TmExpr Σ (m + n) → TyExpr Σ (m + n) → Judgment Σ Γ n Tm
  _⊢_==_    : (Δ : DepCtx Σ m n) → TyExpr Σ (m + n) → TyExpr Σ (m + n) → Judgment Σ Γ n Ty=
  _⊢_==_:>_ : (Δ : DepCtx Σ m n) → TmExpr Σ (m + n) → TmExpr Σ (m + n) → TyExpr Σ (m + n)
            → Judgment Σ Γ n Tm=



{-
A derivation rule consists of a partial function taking a tuple of judgments (of the correct
arities) and returning another judgment. Moreover, a derivation rule is extendable to any other
signature the original signature maps to.

The type [DerivationRulePremises Σ Γ args] represents tuples of judgments of arities [args] (and in
signature [Σ] and with ambient context [Γ])

The type [DerivationRule Σ ar n] represents derivation rules in signature [Σ], of arity [ar] and in
scope [n]. It lives in [Set₁] because it quantifies over arbitrary signatures that [Σ] maps into.
-}

data DerivationRulePremises (Σ : Signature) {n : ℕ} (Γ : Ctx Σ n) : JudgmentArityArgs → Set where
  [] : DerivationRulePremises Σ Γ []
  _,_ : {m : ℕ} {k : JudgmentSort} {args : JudgmentArityArgs}
      → DerivationRulePremises Σ Γ args
      → Judgment Σ Γ m k
      → DerivationRulePremises Σ Γ (args , (m , k))

record DerivationRule (Σ : Signature) (ar : JudgmentArity) : Set₁ where
  field
    rule : {Σ' : Signature} {n : ℕ} → (Σ →Sig Σ') n → (Γ : Ctx Σ' n)
         → DerivationRulePremises Σ' Γ (args ar) → Partial (Judgment Σ' Γ 0 (sort ar))
open DerivationRule public

{- A derivability structure consists of a bunch of derivation rules, indexed by their arities -}

data Tag : Set where
  S T C Eq : Tag

record DerivabilityStructure (Σ : Signature) : Set₁ where
  field
    Rules : Tag → JudgmentArity → Set
    derivationRule : {t : Tag} {ar : JudgmentArity} (r : Rules t ar) → DerivationRule Σ ar
open DerivabilityStructure public


{- We can move the local context to the end of the ambient context -}

module _ {Σ : Signature} {m : ℕ} {Γ : Ctx Σ m} where

  Γ+ : {l : ℕ} (Δ : DepCtx Σ m l) → Ctx Σ (m + l)
  Γ+ ◇ = Γ
  Γ+ (Δ , A) = (Γ+ Δ , A)

  exchangeCtx : {n : ℕ} {k : JudgmentSort} → Judgment Σ Γ n k → Ctx Σ (m + n)
  exchangeCtx (Δ ⊢ A)           = Γ+ Δ
  exchangeCtx (Δ ⊢ u :> A)      = Γ+ Δ
  exchangeCtx (Δ ⊢ A == B)      = Γ+ Δ
  exchangeCtx (Δ ⊢ u == v :> A) = Γ+ Δ

  exchange : {n : ℕ} {k : JudgmentSort} → (j : Judgment Σ Γ n k) → Judgment Σ (exchangeCtx j) 0 k
  exchange (Δ ⊢ A)           = ◇ ⊢ A
  exchange (Δ ⊢ u :> A)      = ◇ ⊢ u :> A
  exchange (Δ ⊢ A == B)      = ◇ ⊢ A == B
  exchange (Δ ⊢ u == v :> A) = ◇ ⊢ u == v :> A


{-
A judgment can be derivable in one different way:
- if it has a trivial local context, then it should be obtained by applying a rule [r] from the
  derivability structure to a list of judgments [js] which are all derivable [js-der] and for which
  the rule is defined [def].

The type [DerivableArgs E js] represents the fact that all of the judgments in [js] are derivables.
The type [Derivable E j] represents the fact that the judgment [j] is derivable.
-}

data Derivable {Σ : Signature} (E : DerivabilityStructure Σ)
     : {m : ℕ} {Γ : Ctx Σ m} {k : JudgmentSort} → Judgment Σ Γ 0 k → Prop

data DerivableArgs {Σ : Signature} (E : DerivabilityStructure Σ) {m : ℕ} {Γ : Ctx Σ m}
     : {ar : JudgmentArityArgs} → DerivationRulePremises Σ Γ ar → Prop where
  []  : DerivableArgs E []
  _,_ : {n : ℕ} {k : JudgmentSort} {j : Judgment Σ Γ n k}
        {ar : JudgmentArityArgs} {js : DerivationRulePremises Σ Γ ar}
        → DerivableArgs E js
        → Derivable E (exchange j)
        → DerivableArgs E (js , j)

data Derivable {Σ} E where
  apr : (t : Tag) {ar : JudgmentArity} (r : Rules E t ar) {m : ℕ} {Γ : Ctx Σ m}
        {js : DerivationRulePremises Σ Γ (args ar)}
        (js-der : DerivableArgs E js) {{def : isDefined (rule (derivationRule E r) idSig Γ js)}}
          → Derivable E (rule (derivationRule E r) idSig Γ js $ def)


{- Special cases of [_,_], used to make Agda not blow up -}

_,0Ty_ : ∀ {Σ} {E} {m} {Γ : Ctx Σ m} {A : TyExpr Σ m}
        {ar : JudgmentArityArgs} {js : DerivationRulePremises Σ Γ ar}
        → DerivableArgs E js
        → Derivable E (◇ ⊢ A)
        → DerivableArgs E (js , ◇ ⊢ A)
djs ,0Ty dj = djs , dj

_,0Ty=_ : ∀ {Σ} {E} {m} {Γ : Ctx Σ m} {A B : _}
        {ar : JudgmentArityArgs} {js : DerivationRulePremises Σ Γ ar}
        → DerivableArgs E js
        → Derivable E (◇ ⊢ A == B)
        → DerivableArgs E (js , ◇ ⊢ A == B)
djs ,0Ty= dj = djs , dj

_,0Tm_ : ∀ {Σ} {E} {m} {Γ : Ctx Σ m} {u : _} {A : _}
        {ar : JudgmentArityArgs} {js : DerivationRulePremises Σ Γ ar}
        → DerivableArgs E js
        → Derivable E (◇ ⊢ u :> A)
        → DerivableArgs E (js , ◇ ⊢ u :> A)
djs ,0Tm dj = djs , dj

_,0Tm=_ : ∀ {Σ} {E} {m} {Γ : Ctx Σ m} {u v : _} {A : _}
        {ar : JudgmentArityArgs} {js : DerivationRulePremises Σ Γ ar}
        → DerivableArgs E js
        → Derivable E (◇ ⊢ u == v :> A)
        → DerivableArgs E (js , ◇ ⊢ u == v :> A)
djs ,0Tm= dj = djs , dj

_,1Ty_ : ∀ {Σ} {E} {m} {Γ : Ctx Σ m} {A} {B}
        {ar : JudgmentArityArgs} {js : DerivationRulePremises Σ Γ ar}
        → DerivableArgs E js
        → Derivable E (exchange ((◇ , A) ⊢ B))
        → DerivableArgs E (js , (◇ , A) ⊢ B)
djs ,1Ty dj = djs , dj

_,1Ty=_ : ∀ {Σ} {E} {m} {Γ : Ctx Σ m} {A} {B C}
        {ar : JudgmentArityArgs} {js : DerivationRulePremises Σ Γ ar}
        → DerivableArgs E js
        → Derivable E (exchange ((◇ , A) ⊢ B == C))
        → DerivableArgs E (js , (◇ , A) ⊢ B == C)
djs ,1Ty= dj = djs , dj

_,1Tm_ : ∀ {Σ} {E} {m} {Γ : Ctx Σ m} {u : _} {A : _} {B : _}
        {ar : JudgmentArityArgs} {js : DerivationRulePremises Σ Γ ar}
        → DerivableArgs E js
        → Derivable E (exchange ((◇ , B) ⊢ u :> A))
        → DerivableArgs E (js , (◇ , B) ⊢ u :> A)
djs ,1Tm dj = djs , dj

_,1Tm=_ : ∀ {Σ} {E} {m} {Γ : Ctx Σ m} {u v : _} {A : _} {B : _}
        {ar : JudgmentArityArgs} {js : DerivationRulePremises Σ Γ ar}
        → DerivableArgs E js
        → Derivable E (exchange ((◇ , B) ⊢ u == v :> A))
        → DerivableArgs E (js , (◇ , B) ⊢ u == v :> A)
djs ,1Tm= dj = djs , dj

infixl 4 _,0Ty_ _,0Ty=_ _,0Tm_ _,0Tm=_
         _,1Ty_ _,1Ty=_ _,1Tm_ _,1Tm=_
