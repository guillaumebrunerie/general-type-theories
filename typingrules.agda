{-# OPTIONS --rewriting --prop #-}

open import common
open import syntx
open import derivability


{- Helper functions to compute the arity of a rule given the arity of the symbol. -}

SStoJS : SyntaxSort → JudgmentSort
SStoJS Ty = Ty
SStoJS Tm = Tm

TArityArgs : SyntaxArityArgs → JudgmentArityArgs
TArityArgs [] = []
TArityArgs (ar , (n , k)) = TArityArgs ar , (n , SStoJS k)

TArity : SyntaxArity → JudgmentArity
TArity ar = (TArityArgs (args ar) , SStoJS (sort ar))

SStoJS= : SyntaxSort → JudgmentSort
SStoJS= Ty = Ty=
SStoJS= Tm = Tm=

CArityArgs : SyntaxArityArgs → JudgmentArityArgs
CArityArgs [] = []
CArityArgs (ar , (n , k)) = CArityArgs ar , (n , SStoJS= k)

CArity : SyntaxArity → JudgmentArity
CArity ar = (CArityArgs (args ar) , SStoJS= (sort ar))

{-
[↑DerivationRule r] extends the derivation rule [r] to an extended signature.
This is easy because derivation rules were designed to be extendable.
-}
↑DerivationRule : {Σ : Signature} {sar : SyntaxArity} {jar : JudgmentArity}
                → DerivationRule Σ jar → DerivationRule (ExtSig Σ sar) jar
rule (↑DerivationRule r) ↑ Γ = rule r (Ext→ ↑) Γ

{- Record combining the typing and congruence rules for a new symbol. -}
record DerivationRules {Σ : Signature} (E : DerivabilityStructure Σ) (ar : SyntaxArity) : Set₁ where
  field
    typingdrule     : DerivationRule (ExtSig Σ ar) (TArity ar)
    congruencedrule : DerivationRule (ExtSig Σ ar) (CArity ar)
open DerivationRules public

{-
[extend E tc] extends the derivability structure [E] to an extended signature, where [tc] is the
typing/congruence rules of a new symbol. We also use a custom data type in order to add the two new
rules, in order to get something readable.
-}

data ExtT (A : JudgmentArity → Set) (sar : SyntaxArity) : JudgmentArity → Set where
  typingrule : ExtT A sar (TArity sar)
  prev : {jar : JudgmentArity} → A jar → ExtT A sar jar

data ExtC (A : JudgmentArity → Set) (sar : SyntaxArity) : JudgmentArity → Set where
  congruencerule : ExtC A sar (CArity sar)
  prev : {jar : JudgmentArity} → A jar → ExtC A sar jar

extend : {Σ : Signature} (E : DerivabilityStructure Σ)
         {ar : SyntaxArity}
         (tc : DerivationRules E ar)
         → DerivabilityStructure (ExtSig Σ ar)

Rules (extend E {ar} tc) S  = Rules E S
Rules (extend E {ar} tc) T  = ExtT (Rules E T) ar
Rules (extend E {ar} tc) C  = ExtC (Rules E C) ar
Rules (extend E {ar} tc) Eq = Rules E Eq
derivationRule (extend E tc) {t = S} r = ↑DerivationRule (derivationRule E r)
derivationRule (extend E tc) {t = T} (prev r) = ↑DerivationRule (derivationRule E r)
derivationRule (extend E tc) {t = T} typingrule = typingdrule tc
derivationRule (extend E tc) {t = C} (prev r) = ↑DerivationRule (derivationRule E r)
derivationRule (extend E tc) {t = C} congruencerule = congruencedrule tc
derivationRule (extend E tc) {t = Eq} r = ↑DerivationRule (derivationRule E r)

-- data Ext (A : Tag → JudgmentArity → Set) (sar : SyntaxArity) : Tag → JudgmentArity → Set where
--   typingrule : Ext A sar T (TArity sar)
--   congruencerule : Ext A sar C (CArity sar)
--   prev : {t : Tag} {jar : JudgmentArity} → A t jar → Ext A sar t jar

-- extend : {Σ : Signature} (E : DerivabilityStructure Σ)
--          {ar : SyntaxArity}
--          (tc : DerivationRules E ar 0)
--          → DerivabilityStructure (ExtSig Σ ar)
-- Rules (extend E {ar} tc) = Ext (Rules E) ar
-- derivationRule (extend E tc) typingrule = typingdrule tc
-- derivationRule (extend E tc) congruencerule = congruencedrule tc
-- derivationRule (extend E tc) (prev r) = ↑DerivationRule (derivationRule E r)


{- Typing rules for basic metavariables (simply a derivable type in the empty context) -}

record BMTypingRule {Σ : Signature} (E : DerivabilityStructure Σ) : Set where
  constructor _/_
  field
    type : TyExpr Σ 0
    der : Derivable E {Γ = ◇} (◇ ⊢ type)
open BMTypingRule public

{- The derivation rules corresponding to a basic metavariable (on the extended signature). -}

BMRules : {Σ : Signature} {E : DerivabilityStructure Σ}
          (t : BMTypingRule E)
          → DerivationRules E ([] , Tm)
rule (typingdrule     (BMRules t)) ↑ Γ [] = return (◇ ⊢ (↑ $ new) []
                                                      :> ↑Expr (Ext→ ↑) (weaken0 (type t)))
rule (congruencedrule (BMRules t)) ↑ Γ [] = return (◇ ⊢ (↑ $ new) [] == (↑ $ new) []
                                                      :> ↑Expr (Ext→ ↑) (weaken0 (type t)))



-- --------------    -----------------
--   Γ ⊢ s : A         Γ ⊢ s = s : A



{-
The premises of a typing rule for a metavariables form essentially a list of typing rules for basic
metavariables in increasingly extended signatures. There are two different ways to order the premises:
- either we have the first premise, and then the rest in an extended signature,
- or we have all but the last premises, and then the last one in a signature extended by all the
  previous ones.

The first option looks simpler, but we use the second option because we will need to talk about
multiple substitution later anyway, and also it allows us to keep typing rules in the empty context.

The type [MTypingRulePremises E n] represents a list of length [n] of such premises. It is defined
simultaneously with multiple substitution: [extend^BM E ts] represents the derivability structure
[E] extended by all the basic metavariables of [ts].
-}

data MTypingRulePremises : {Σ : Signature} (E : DerivabilityStructure Σ) (n : ℕ) → Set

extend^BM : {Σ : Signature} (E : DerivabilityStructure Σ) {n : ℕ} (ts : MTypingRulePremises E n)
          → DerivabilityStructure (ExtSig^ Σ (MArityArgs n))

data MTypingRulePremises where
  [] : ∀ {Σ} {E : DerivabilityStructure Σ} → MTypingRulePremises E 0
  _,_ : ∀ {Σ} {E : DerivabilityStructure Σ} {n : ℕ}
      → (ts : MTypingRulePremises E n)
      → (t : BMTypingRule (extend^BM E ts))
      → MTypingRulePremises E (suc n)

extend^BM E [] = E
extend^BM E (ts , t) = extend (extend^BM E ts) (BMRules t)

{-
[MTypingRule E n k] represents typing rules in derivability structure [E] for a metavariable of
arity (n , k).
There are two cases depending on [k]:
- if [k] is [Ty], then we simply need a list of premises,
- if [k] is [Tm], then we need a list of premises and a type for the conclusion, in the correctly
  extended derivability structure.
-}

data MTypingRule {Σ : Signature} (E : DerivabilityStructure Σ) (n : ℕ) : (k : SyntaxSort) → Set where
  Ty : MTypingRulePremises E n → MTypingRule E n Ty
  Tm : (ts : MTypingRulePremises E n) → BMTypingRule (extend^BM E ts) → MTypingRule E n Tm

{-
Γ, n : ℕ, y : P n ⊢ dS : P (n + 1)

◇ ⊢ _n : ℕ
◇ ⊢ _y : P _n
----------------------------
◇ ⊢ dS(_n , _y) : P (_n + 1)


Γ ⊢ n = m : ℕ
Γ ⊢ u = v : P n
-----------
Γ ⊢ dS(n , u) = dS(m , v) : P (n + 1)


Γ ⊢ 3 : ℕ
Γ ⊢ u : P 3
~~~>
Γ ⊢ dS(3 , u) : P (3 + 1)


(n : ℕ, y : P n)

-}

{-
The derivation rules associated to a typing rule for a metavariable.
-}

MTypingRule-TArgs : {Σ Σ' : Signature} (E : DerivabilityStructure Σ) {n m : ℕ} (↑ : (Σ →Sig Σ') m) {Γ : Ctx Σ' m}
                   (ts : MTypingRulePremises E n) (js : DerivationRulePremises Σ' Γ (TArityArgs (MArityArgs n)))
                   → Partial (Args Σ' m (MArityArgs n))
MTypingRule-TArgs E ↑ [] [] = return []
MTypingRule-TArgs E ↑ (ts , t) (js , ◇ ⊢ a :> A) = do
  as ← MTypingRule-TArgs E ↑ ts js
  assume (A ≡ ↑Expr (SubstM ↑ as) (weaken0 (type t)))
  return (as , a)

MTypingRule-TRule : {Σ : Signature} (E : DerivabilityStructure Σ) {n : ℕ} {k : SyntaxSort}
                    (t : MTypingRule E n k)
                    → DerivationRule (ExtSig Σ (MArity n k)) (TArity (MArity n k))
rule (MTypingRule-TRule E (Ty ts)) ↑ Γ js = do
  as ← MTypingRule-TArgs E (Ext→ ↑) ts js
  return (◇ ⊢ (↑ $ new) as)
rule (MTypingRule-TRule E (Tm ts t)) ↑ Γ js = do
  as ← MTypingRule-TArgs E (Ext→ ↑) ts js
  return (◇ ⊢ (↑ $ new) as :> ↑Expr (SubstM (Ext→ ↑) as) (weaken0 (type t)))


MTypingRule-CArgs : {Σ Σ' : Signature} (E : DerivabilityStructure Σ) {n m : ℕ} (↑ : (Σ →Sig Σ') m) {Γ : Ctx Σ' m}
                   (ts : MTypingRulePremises E n) (js : DerivationRulePremises Σ' Γ (CArityArgs (MArityArgs n)))
                   → Partial (Args Σ' m (MArityArgs n) × Args Σ' m (MArityArgs n))
MTypingRule-CArgs E ↑ [] [] = return ([] , [])
MTypingRule-CArgs E ↑ (ts , t) (js , ◇ ⊢ a == a' :> A) = do
  (as , as') ← MTypingRule-CArgs E ↑ ts js
  assume (A ≡ ↑Expr (SubstM ↑ as) (weaken0 (type t)))
  return ((as , a) , (as' , a'))

MTypingRule-CRule : {Σ : Signature} (E : DerivabilityStructure Σ) {n : ℕ} {k : SyntaxSort}
                    (t : MTypingRule E n k)
                    → DerivationRule (ExtSig Σ (MArity n k)) (CArity (MArity n k))
rule (MTypingRule-CRule E (Ty ts)) ↑ Γ js = do
  (as , as') ← MTypingRule-CArgs E (Ext→ ↑) ts js
  return (◇ ⊢ (↑ $ new) as == (↑ $ new) as')
rule (MTypingRule-CRule E (Tm ts t)) ↑ Γ js = do
  (as , as') ← MTypingRule-CArgs E (Ext→ ↑) ts js
  return (◇ ⊢ (↑ $ new) as == (↑ $ new) as' :> ↑Expr (SubstM (Ext→ ↑) as) (weaken0 (type t)))


MRules : {Σ : Signature} {E : DerivabilityStructure Σ} {n : ℕ} {k : SyntaxSort}
                    (t : MTypingRule E n k)
                    → DerivationRules E (MArity n k)
typingdrule (MRules t) = MTypingRule-TRule _ t
congruencedrule (MRules t) = MTypingRule-CRule _ t



{-
General typing rules are very similar to typing rules of metavariables, except that they are using
[MTypingRule] instead of [BMTypingRule] for the premises.
-}

data TypingRulePremises : {Σ : Signature} (E : DerivabilityStructure Σ) (args : SyntaxArityArgs) → Set

extend^M : {Σ : Signature} (E : DerivabilityStructure Σ) {args : SyntaxArityArgs} (ts : TypingRulePremises E args) → DerivabilityStructure (ExtSig^ Σ args)

data TypingRulePremises where
  [] : ∀ {Σ} {E : DerivabilityStructure Σ} → TypingRulePremises E []
  _,_ : ∀ {Σ} {E : DerivabilityStructure Σ} {args : SyntaxArityArgs} {m : ℕ} {k : SyntaxSort}
      → (ts : TypingRulePremises E args)
      → (t : MTypingRule (extend^M E ts) m k)
      → TypingRulePremises E (args , (m , k))

extend^M E [] = E
extend^M E (ts , t) = extend (extend^M E ts) (MRules t)

data TypingRule {Σ : Signature} (E : DerivabilityStructure Σ) (args : SyntaxArityArgs) : (k : SyntaxSort) → Set where
  Ty : TypingRulePremises E args → TypingRule E args Ty
  Tm : (ts : TypingRulePremises E args) → BMTypingRule (extend^M E ts) → TypingRule E args Tm


{- The derivation rules associated to a typing rule. -}

{- List of all the last [n] variables in scope [m + n] -}
Vars : {Σ : Signature} {n : ℕ} (m : ℕ) → Args Σ (m + n) (MArityArgs n)
Vars {n = zero} m = []
Vars {n = suc n} m = weakenA {{≤-+ {m + n} {1}}} last (Vars m) , var last

{-
[check-DepCtx ↑ as ts Δ] checks that the premises [ts] correspond to the dependent context [Δ],
where [as] corresponds to the interpretations of the metavariables.
-}
check-DepCtx : {Σ Σ' : Signature} {m n : ℕ} {args : SyntaxArityArgs}
               {E : DerivabilityStructure (ExtSig^ Σ args)}
               → (Σ →Sig Σ') m → Args Σ' m args
               → MTypingRulePremises E n → DepCtx Σ' m n → Prop
check-DepCtx ↑ as [] ◇ = ⊤
check-DepCtx {m = m} {n = suc n} ↑ as (ts , t) (Δ , A) =
  ΣP (check-DepCtx ↑ as ts Δ)
  (λ _ → A ≡ ↑Expr (SubstM (liftSig ↑) (weakenAL as)) (↑Expr (SubstM idSig (Vars m)) (weaken0 (type t))))

TypingRule-TArgs : {Σ Σ' : Signature} (E : DerivabilityStructure Σ) {args : SyntaxArityArgs} {m : ℕ} (↑ : (Σ →Sig Σ') m) {Γ : Ctx Σ' m}
                   (ts : TypingRulePremises E args) (js : DerivationRulePremises Σ' Γ (TArityArgs args))
                   → Partial (Args Σ' m args)
TypingRule-TArgs E ↑ [] [] = return []
TypingRule-TArgs E ↑ (ts , Ty t's) (js , Δ ⊢ A) = do
  as ← TypingRule-TArgs E ↑ ts js
  assume (check-DepCtx ↑ as t's Δ)
  return (as , A)
TypingRule-TArgs E {m = m} ↑ (ts , Tm t's t) (js , Δ ⊢ u :> A) = do
  as ← TypingRule-TArgs E ↑ ts js
  assume (check-DepCtx ↑ as t's Δ)
  assume (A ≡ ↑Expr (SubstM (liftSig ↑) (weakenAL as)) (↑Expr (SubstM idSig (Vars m)) (weaken0 (type t))))
  return (as , u)

TypingRule-TRule : {Σ : Signature} (E : DerivabilityStructure Σ) {args : SyntaxArityArgs} {k : SyntaxSort}
                   (t : TypingRule E args k)
                   → DerivationRule (ExtSig Σ (args , k)) (TArity (args , k))
rule (TypingRule-TRule E (Ty ts)) ↑ Γ js = do
  as ← TypingRule-TArgs E (Ext→ ↑) ts js
  return (◇ ⊢ (↑ $ new) as)
rule (TypingRule-TRule E (Tm ts t)) ↑ Γ js = do
  as ← TypingRule-TArgs E (Ext→ ↑) ts js
  return (◇ ⊢ (↑ $ new) as :> ↑Expr (SubstM (Ext→ ↑) as) (weaken0 (type t)))


TypingRule-CArgs : {Σ Σ' : Signature} (E : DerivabilityStructure Σ) {args : SyntaxArityArgs} {m : ℕ} (↑ : (Σ →Sig Σ') m) {Γ : Ctx Σ' m}
                   (ts : TypingRulePremises E args) (js : DerivationRulePremises Σ' Γ (CArityArgs args))
                   → Partial (Args Σ' m args × Args Σ' m args)
TypingRule-CArgs E ↑ [] [] = return ([] , [])
TypingRule-CArgs E {args = args , (n , Ty)} {m} ↑ (ts , Ty t's) (js , Δ ⊢ A == A') = do
  (as , as') ← TypingRule-CArgs E ↑ ts js
  assume (check-DepCtx ↑ as t's Δ)
  return ((as , A) , (as' , A'))
TypingRule-CArgs E {args = args , (n , Tm)} {m} ↑ (ts , Tm t's t) (js , Δ ⊢ u == u' :> A) = do
  (as , as') ← TypingRule-CArgs E ↑ ts js
  assume (check-DepCtx ↑ as t's Δ)
  assume (A ≡ ↑Expr (SubstM (liftSig ↑) (weakenAL as)) (↑Expr (SubstM idSig (Vars m)) (weaken0 (type t))))
  return ((as , u) , (as' , u'))


TypingRule-CRule : {Σ : Signature} (E : DerivabilityStructure Σ) {args : SyntaxArityArgs} {k : SyntaxSort}
                   (t : TypingRule E args k)
                   → DerivationRule (ExtSig Σ (args , k)) (CArity (args , k))
rule (TypingRule-CRule E (Ty ts)) ↑ Γ js = do
  (as , as') ← TypingRule-CArgs E (Ext→ ↑) ts js
  return (◇ ⊢ (↑ $ new) as == (↑ $ new) as')
rule (TypingRule-CRule E (Tm ts t)) {n = n} ↑ Γ js = do
  (as , as') ← TypingRule-CArgs E (Ext→ ↑) ts js
  return (◇ ⊢ (↑ $ new) as == (↑ $ new) as' :> ↑Expr (SubstM (Ext→ ↑) as) (weaken0 (type t)))


TRules : {Σ : Signature} {E : DerivabilityStructure Σ} {ar : SyntaxArity}
        (t : TypingRule E (args ar) (sort ar))
        → DerivationRules E ar
typingdrule (TRules t) = TypingRule-TRule _ t
congruencedrule (TRules t) = TypingRule-CRule _ t


{-
Γ ⊢ A == A'
Γ , x : A ⊢ B == B'
--------------------
Γ ⊢ Π A B == Π A' B'
-}

{- Equality rules -}

{-
[extendE E tc] extends the derivability structure with one single (equality) rule
-}

data ExtE (A : JudgmentArity → Set) (nar : JudgmentArity) : JudgmentArity → Set where
  equalityrule : ExtE A nar nar
  prev : {jar : JudgmentArity} → A jar → ExtE A nar jar

extendE : {Σ : Signature} (E : DerivabilityStructure Σ)
          {ar : JudgmentArity}
          (tc : DerivationRule Σ ar)
          → DerivabilityStructure Σ
Rules (extendE E {ar} tc) S = Rules E S
Rules (extendE E {ar} tc) T = Rules E T
Rules (extendE E {ar} tc) C = Rules E C
Rules (extendE E {ar} tc) Eq = ExtE (Rules E Eq) ar
derivationRule (extendE E tc) {S} r = derivationRule E r
derivationRule (extendE E tc) {T} r = derivationRule E r
derivationRule (extendE E tc) {C} r = derivationRule E r
derivationRule (extendE E tc) {Eq} (prev r) = derivationRule E r
derivationRule (extendE E tc) {Eq} equalityrule = tc

-- data ExtE (A : Tag → JudgmentArity → Set) (nar : JudgmentArity) : Tag → JudgmentArity → Set where
--   equalityrule : ExtE A nar Eq nar
--   prev : {t : Tag} {jar : JudgmentArity} → A t jar → ExtE A nar t jar

-- extendE : {Σ : Signature} (E : DerivabilityStructure Σ)
--           {ar : JudgmentArity}
--           (tc : {n : ℕ} → DerivationRule Σ ar n)
--           → DerivabilityStructure Σ
-- Rules (extendE E {ar} tc) = ExtE (Rules E) ar
-- derivationRule (extendE E tc) (prev r) = derivationRule E r
-- derivationRule (extendE E tc) equalityrule = tc

record TermEquality {Σ : Signature} (E : DerivabilityStructure Σ) : Set where
  constructor _<:_/_//_/_
  field
    type : TyExpr Σ 0
    term1 : TmExpr Σ 0
    der1 : Derivable E {Γ = ◇} (◇ ⊢ term1 :> type)
    term2 : TmExpr Σ 0
    der2 : Derivable E {Γ = ◇} (◇ ⊢ term2 :> type)
open BMTypingRule public

data EqualityRule {Σ : Signature} (E : DerivabilityStructure Σ) (args : SyntaxArityArgs) : (k : JudgmentSort) → Set where
  Ty= : (ts : TypingRulePremises E args) (A B : BMTypingRule (extend^M E ts)) → EqualityRule E args Ty=
  Tm= : (ts : TypingRulePremises E args) (A : TermEquality (extend^M E ts)) → EqualityRule E args Tm=

ERule : {Σ : Signature} (E : DerivabilityStructure Σ) {args : SyntaxArityArgs} {k : JudgmentSort}
        → EqualityRule E args k
        → DerivationRule Σ (TArityArgs args , k)
rule (ERule E (Ty= ts A B)) ↑ Γ js = do
  as ← TypingRule-TArgs E ↑ ts js
  return (◇ ⊢ (↑Expr (SubstM ↑ as) (weaken0 (A .type))) == (↑Expr (SubstM ↑ as) (weaken0 (B .type))))
rule (ERule E (Tm= ts (A <: u / _ // v / _))) ↑ Γ js = do
  as ← TypingRule-TArgs E ↑ ts js
  return (◇ ⊢ (↑Expr (SubstM ↑ as) (weaken0 u)) == (↑Expr (SubstM ↑ as) (weaken0 u)) :> ↑Expr (SubstM ↑ as) (weaken0 A))
