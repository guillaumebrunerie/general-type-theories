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
Judgments are indexed by the signature, their context, and their sort.

We can see judgments as consisting of two contexts, one normal context (the ambient context) and
then one dependent context. The reason is that all typing rules occur in an ambient context which
never changes, and sometimes add new assumptions (to the dependent context). Therefore we will never
have to check that the ambient contexts are equal, it will be forced by the typing.

Indexing judgments by sorts is very good to get rid of absurd cases, when giving typing rules and
that some judgments are supposed to have certain sorts.
-}

data Judgment (Σ : Signature) {n : ℕ} (Γ : Ctx Σ n) (m : ℕ) : JudgmentSort → Set where
  _⊢_ : (Δ : DepCtx Σ n m) → TyExpr Σ (n + m) → Judgment Σ Γ m Ty
  _⊢_:>_ : (Δ : DepCtx Σ n m) → TmExpr Σ (n + m) → TyExpr Σ (n + m) → Judgment Σ Γ m Tm
  _⊢_==_ : (Δ : DepCtx Σ n m) → TyExpr Σ (n + m) → TyExpr Σ (n + m) → Judgment Σ Γ m Ty=
  _⊢_==_:>_ : (Δ : DepCtx Σ n m) → TmExpr Σ (n + m) → TmExpr Σ (n + m) → TyExpr Σ (n + m)
            → Judgment Σ Γ m Tm=


{-
In order to deal with extensions of signatures, we need a notion of map between signatures. There
are a few possible options:
- Mapping symbols to symbols: not strong enough, as later we need to map a symbol s(-) to the
  expression s(a, -)
- Mapping expressions to expressions: too strong, makes it impossible to look inside expressions
- Mapping symbols to expression-building function: this is the approach we take. A symbol will be
  mapped to a function of the corresponding arity between expressions of the codomain signature.

We need sometimes to restrict them to expressions in a certain scope (bounded below). This happens
for instance when turning typing rules to partial functions on the syntax, we replace something by
a specific term which lives in a scope, so the map between signatures does not work for a lower
scope. We need to have it simply bounded below (as opposed to having a fixed scope) otherwise we
cannot map expressions to expressions (they may bind new variables).
-}

record Sub (Σ Σ' : Signature) (n : ℕ) : Set where
  constructor make⊂
  field
    _$_ : {k : ℕ} {{_ : n ≤ k}} {ar : SyntaxArity} (s : Symbols Σ ar) → Args Σ' k (args ar) → Expr Σ' k (sort ar)
open Sub public

{- Identity map -}

id⊂ : {n : ℕ} {Σ : Signature} → Sub Σ Σ n
id⊂ $ s = sym s

{- Lifting at a higher scope -}

liftSub : {n m : ℕ} {Σ Σ' : Signature} {{_ : n ≤ m}} → Sub Σ Σ' n → Sub Σ Σ' m
(liftSub ↑ $ s) x = (↑ $ s) x

{- Lifting of a map between signatures to expressions -}

↑Expr : {Σ Σ' : Signature} {n : ℕ} {k : SyntaxSort} → Sub Σ Σ' n → Expr Σ n k → Expr Σ' n k
↑Args : {Σ Σ' : Signature} {n : ℕ} {args : SyntaxArityArgs} → Sub Σ Σ' n → Args Σ n args → Args Σ' n args

↑Expr ↑ (var x) = var x
↑Expr ↑ (sym s x) = (↑ $ s) (↑Args ↑ x)

↑Args ↑ [] = []
↑Args ↑ (e ∷ es) = ↑Expr (liftSub ↑) e ∷ ↑Args ↑ es


{-
A raw derivation rule is indexed by the signature, the ambient context and the arity of the rule.
It is some sort of iterated partial function from judgments to derivation rules.
More precisely:
- if there are no premises, then it is simply a judgment without dependent context (the conclusion)
- if there is at least one premise, then it is a partial function for judgments corresponding to
  the first premise, to raw derivation rules corresponding to the rest of the premises.
-}

data RawDerivationRule (Σ : Signature) {n : ℕ} (Γ : Ctx Σ n)
    : (args : JudgmentArityArgs) (k : JudgmentSort) → Set₁ where
  last : {k : JudgmentSort} → Judgment Σ Γ 0 k → RawDerivationRule Σ Γ [] k
  next : {m : ℕ} {k kfin : JudgmentSort} {args : JudgmentArityArgs}
       → (Judgment Σ Γ m k → Partial (RawDerivationRule Σ Γ args kfin))
       → RawDerivationRule Σ Γ ((m , k) ∷ args) kfin

{-
A derivation rule are indexed by the signature, the arity of the rule, and the length of the ambient
context.
It consists of a raw derivation rule for every extended signature and every possible ambient context.
-}

record DerivationRule (Σ : Signature) (ar : JudgmentArity) (n : ℕ) : Set₁ where
  field
    rule : {Σ' : Signature} → Sub Σ Σ' n → (Γ : Ctx Σ' n)
         → RawDerivationRule Σ' Γ (args ar) (sort ar)
open DerivationRule public


{- A derivability structure consists of a bunch of derivation rules, indexed by their arities -}

record DerivabilityStructure (Σ : Signature) : Set₁ where
  field
    Rules : JudgmentArity → Set
    derivationRule : {ar : JudgmentArity} (r : Rules ar) {n : ℕ} → DerivationRule Σ ar n
open DerivabilityStructure public


{- We can move types from the dependent context to the ambient context -}

module _ {Σ : Signature} {n : ℕ} {Γ : Ctx Σ n} {m : ℕ} {k : JudgmentSort} where

  exchangeCtx : Judgment Σ Γ (suc m) k → Ctx Σ (suc n)
  exchangeCtx ((X , Δ) ⊢ A)           = (Γ , X)
  exchangeCtx ((X , Δ) ⊢ u :> A)      = (Γ , X)
  exchangeCtx ((X , Δ) ⊢ A == B)      = (Γ , X)
  exchangeCtx ((X , Δ) ⊢ u == v :> A) = (Γ , X)

  exchange : (j : Judgment Σ Γ (suc m) k) → Judgment Σ {n = suc n} (exchangeCtx j) m k
  exchange ((X , Δ) ⊢ A)           = Δ ⊢ A
  exchange ((X , Δ) ⊢ u :> A)      = Δ ⊢ u :> A
  exchange ((X , Δ) ⊢ A == B)      = Δ ⊢ A == B
  exchange ((X , Δ) ⊢ u == v :> A) = Δ ⊢ u == v :> A


{- Derivability

[Derivable E j] is true iff the judgment [j] is derivable in [E]. There are two ways a judgment can
be derivable:
- either it is a judgment with a non-trivial dependent context, in which case we simply move the
  first type of the dependent context to the ambient context and try again,
- or it’s a type with a trivial dependent context, in which case we apply a typing rule.

[Apply E r j] is true iff the judgment [j] (with trivial dependent context) can be obtained using
the rule [r] to derivable judgments:
- either the rule is of the form [last j], in which case it is trivial
- or the rule is of the form [next f], in which case we need a judgment [j] corresponding to the
  first argument of [f], we need [f j] to be defined, [j] to be derivable, and we recursively use
  [Apply] to [f j].
-}

data Derivable {Σ : Signature} (E : DerivabilityStructure Σ)
     : {n : ℕ} {Γ : Ctx Σ n} {m : ℕ} {k : JudgmentSort} → Judgment Σ Γ m k → Prop

data Apply {Σ : Signature} (E : DerivabilityStructure Σ)
           {n : ℕ} {Γ : Ctx Σ n} {k : JudgmentSort}
           : {ar : JudgmentArityArgs} → RawDerivationRule Σ Γ ar k → Judgment Σ Γ 0 k → Prop where
  last : (j : Judgment Σ Γ 0 k) → Apply E (last j) j
  next : {m : ℕ} {ar : _} (f : Judgment Σ Γ m k → Partial (RawDerivationRule Σ Γ ar k)) (jj : Judgment Σ Γ 0 k) (j : Judgment Σ Γ m k)
       → (def : isDefined (f j))
       → Derivable E j
       → Apply E (f j $ def) jj
       → Apply E (next f) jj

data Derivable {Σ} E where
  apply : {n : ℕ} {Γ : Ctx Σ n} {k : JudgmentSort} {j : Judgment Σ Γ 0 k}
          {args : JudgmentArityArgs} (r : Rules E (mkarity args k))
          → Apply E (rule (derivationRule E r) id⊂ Γ) j
          → Derivable E j
  flat : {n : ℕ} {Γ : Ctx Σ n} {m : ℕ} {k : JudgmentSort} {j : Judgment Σ Γ (suc m) k} → Derivable E (exchange j) → Derivable E j


{- We now define the structural rules -}

module _ (Σ : Signature) where

  VarRule : {n : ℕ} (k : ℕ) → DerivationRule Σ (mkarity ((0 , Ty) ∷ []) Tm) n
  rule (VarRule k) ↑ Γ =
    next (λ { (◇ ⊢ A) → do
      lift (k' , A') ← get k Γ
      assume (A ≡ A')
      return (last (◇ ⊢ var k' :> A))})

  ConvRule : {n : ℕ} → DerivationRule Σ (mkarity ((0 , Tm) ∷ (0 , Ty=) ∷ []) Tm) n
  rule ConvRule ↑ Γ =
    (next (λ { (◇ ⊢ u :> A) → return
    (next (λ { (◇ ⊢ A' == B) → do
      assume (A ≡ A')
      return
       (last (◇ ⊢ u :> B))}))}))

  ConvEqRule : {n : ℕ} → DerivationRule Σ (mkarity ((0 , Tm=) ∷ (0 , Ty=) ∷ []) Tm=) n
  rule ConvEqRule ↑ Γ =
    (next (λ { (◇ ⊢ u == v :> A) → return
    (next (λ { (◇ ⊢ A' == B) → do
      assume (A ≡ A')
      return
       (last (◇ ⊢ u == v :> B))}))}))

  TyReflRule : {n : ℕ} → DerivationRule Σ (mkarity ((0 , Ty) ∷ []) Ty=) n
  rule TyReflRule ↑ Γ = next (λ {(◇ ⊢ A) → return (last (◇ ⊢ A == A))})

  {-
  This one and the next one could be simplified, I just wanted to check that the full version is
  still doable
  -}

  TySymmRule : {n : ℕ} → DerivationRule Σ (mkarity ((0 , Ty) ∷ (0 , Ty) ∷ (0 , Ty=) ∷ []) Ty=) n
  rule TySymmRule ↑ Γ =
    (next (λ {(◇ ⊢ A) → return
    (next (λ {(◇ ⊢ B) → return
    (next (λ {(◇ ⊢ A' == B') → do
      assume (A ≡ A')
      assume (B ≡ B')
      return (last (◇ ⊢ B' == A'))}))}))}))

  TyTranRule : {n : ℕ} → DerivationRule Σ (mkarity ((0 , Ty) ∷ (0 , Ty) ∷ (0 , Ty) ∷ (0 , Ty=) ∷ (0 , Ty=) ∷ []) Ty=) n
  rule TyTranRule ↑ Γ =
    (next (λ {(◇ ⊢ A) → return
    (next (λ {(◇ ⊢ B) → return
    (next (λ {(◇ ⊢ C) → return
    (next (λ {(◇ ⊢ A' == B') → do
      assume (A ≡ A')
      assume (B ≡ B')
      return
        (next (λ {(◇ ⊢ B'' == C') → do
          assume (B' ≡ B'')
          assume (C ≡ C')
          return (last (◇ ⊢ A' == C'))}))}))}))}))}))

  TmReflRule : {n : ℕ} → DerivationRule Σ (mkarity ((0 , Tm) ∷ []) Tm=) n
  rule TmReflRule ↑ Γ = next (λ {(◇ ⊢ u :> A) → return (last (◇ ⊢ u == u :> A))})

  TmSymmRule : {n : ℕ} → DerivationRule Σ (mkarity ((0 , Tm=) ∷ []) Tm=) n
  rule TmSymmRule ↑ Γ = next (λ {(◇ ⊢ u == v :> A) → return (last (◇ ⊢ v == u :> A))})

  TmTranRule : {n : ℕ} → DerivationRule Σ (mkarity ((0 , Tm=) ∷ (0 , Tm=) ∷ []) Tm=) n
  rule TmTranRule ↑ Γ =
    (next (λ {(◇ ⊢ u == v :> A) → return
    (next (λ {(◇ ⊢ v' == w :> A') → do
      assume (v ≡ v')
      assume (A ≡ A')
      return (last (◇ ⊢ u == w :> A))}))}))

  {-
  Small hack to make our life easier, the implicit argument [ar] of [StructuralRulesType] is
  automatically inferred from the definition of [StructuralRules], but for that they need to be
  mutually recursive
  -}

  StructuralRules : DerivabilityStructure Σ

  data StructuralRulesType : {ar : JudgmentArity} → Set where
    var : (k : ℕ) → StructuralRulesType
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


{-
[ExtSig Σ ar] extends the signature [Σ] by an arity [ar], and [extend E t c] gives a derivability
structure on the extended signature, where [t] and [c] are the typing/congruence rules of the new
symbol. We first need to compute the arities of those rules.
-}

SStoJS : SyntaxSort → JudgmentSort
SStoJS Ty = Ty
SStoJS Tm = Tm

SStoJS= : SyntaxSort → JudgmentSort
SStoJS= Ty = Ty=
SStoJS= Tm = Tm=

TCArityArgs : SyntaxArityArgs → JudgmentArityArgs
TCArityArgs [] = []
TCArityArgs ((n , k) ∷ ar) = (n , SStoJS k) ∷ TCArityArgs ar

TArity : SyntaxArity → JudgmentArity
args (TArity ar) = TCArityArgs (args ar)
sort (TArity ar) = SStoJS (sort ar)

CArity : SyntaxArity → JudgmentArity
args (CArity ar) = TCArityArgs (args ar)
sort (CArity ar) = SStoJS= (sort ar)

{-
The type extending signatures. In order to add a symbol only at the correct arity we use an
inductive family (another possibility would be to use decidable equality on the symbols but that’s
ugly).
-}

ExtSig : Signature → SyntaxArity → Signature
Symbols (ExtSig Σ ar) = ExtSigSymbols  module _ where
  data ExtSigSymbols : SyntaxArity → Set where
    prev : {ar' : SyntaxArity} → Symbols Σ ar' → ExtSigSymbols ar'
    new : ExtSigSymbols ar

{- If an extended signature maps to [Σ'], then the original signature too. -}
⊂Ext : {Σ Σ' : Signature} {ar : SyntaxArity} {n : ℕ} → Sub (ExtSig Σ ar) Σ' n → Sub Σ Σ' n
⊂Ext ↑ $ s = ↑ $ (prev s)

{-
We extend derivation rules to extended signatures.
Easy because derivation rules are designed to be extendable.
-}
↑DerivationRule : {Σ : Signature} {ar : SyntaxArity} {ar' : JudgmentArity} {n : ℕ}
                → DerivationRule Σ ar' n → DerivationRule (ExtSig Σ ar) ar' n
rule (↑DerivationRule r) ↑ Γ = rule r (⊂Ext ↑) Γ

{-
The extension of the derivability structure.
We also use a custom data type in order to add the two new rules.
-}
extend : {Σ : Signature} (E : DerivabilityStructure Σ)
         {ar : SyntaxArity}
         (t : {n : ℕ} → DerivationRule (ExtSig Σ ar) (TArity ar) n)
         (c : {n : ℕ} → DerivationRule (ExtSig Σ ar) (CArity ar) n)
         → DerivabilityStructure (ExtSig Σ ar)
Rules (extend E {ar} t c) = Ext (Rules E) ar  module _ where
  data Ext (A : JudgmentArity → Set) (ar : SyntaxArity) : JudgmentArity → Set where
    prev : {ar' : JudgmentArity} → A ar' → Ext A ar ar'
    typingrule : Ext A ar (TArity ar)
    congruencerule : Ext A ar (CArity ar)
derivationRule (extend E t c) (prev r) = ↑DerivationRule (derivationRule E r)
derivationRule (extend E t c) typingrule = t
derivationRule (extend E t c) congruencerule = c


{- Typing rules for basic metavariables (simply a derivable type in the empty context) -}

record BMTypingRule {Σ : Signature} (E : DerivabilityStructure Σ) : Set where
  constructor bmtypingrule
  field
    type : TyExpr Σ 0
    der : Derivable E {Γ = ◇} (◇ ⊢ type)
open BMTypingRule public

{- Arities of basic metavariables and of the corresponding typing rules -}

BMArity : SyntaxArity
args BMArity = []
sort BMArity = Tm

BMArityJ : JudgmentArity
args BMArityJ = []
sort BMArityJ = Tm

BMArityJ= : JudgmentArity
args BMArityJ= = []
sort BMArityJ= = Tm=

{- The derivation rules corresponding to a basic metavariable (on the extended signature). -}

BMTypingRule-TRule : {Σ : Signature} (E : DerivabilityStructure Σ)
                     (t : BMTypingRule E) {n : ℕ}
                     → DerivationRule (ExtSig Σ BMArity) BMArityJ n
rule (BMTypingRule-TRule E t) ↑ Γ = last (◇ ⊢ (↑ $ new) [] :> ↑Expr (⊂Ext ↑) (weaken^ (type t)))

BMTypingRule-CRule : {Σ : Signature} (E : DerivabilityStructure Σ)
                     (t : BMTypingRule E) {n : ℕ}
                     → DerivationRule (ExtSig Σ BMArity) BMArityJ= n
rule (BMTypingRule-CRule E t) ↑ Γ = last (◇ ⊢ (↑ $ new) [] == (↑ $ new) [] :> ↑Expr (⊂Ext ↑) (weaken^ (type t)))


{- Arities of metavariables and of the corresponding typing rules -}

MArityArgs : ℕ → SyntaxArityArgs
MArityArgs zero = []
MArityArgs (suc n) = (0 , Tm) ∷ MArityArgs n

MArity : ℕ → SyntaxSort → SyntaxArity
args (MArity n k) = MArityArgs n
sort (MArity n k) = k

MArityArgsJ : ℕ → JudgmentArityArgs
MArityArgsJ zero = []
MArityArgsJ (suc n) = (0 , Tm) ∷ MArityArgsJ n

MArityJ : ℕ → SyntaxSort → JudgmentArity
args (MArityJ n k) = MArityArgsJ n
sort (MArityJ n k) = SStoJS k

{-
Typing rules for metavariables.
The base cases are
- it’s a type: nothing to do,
- it’s a term: we give a typing rule for a basic metavariable.
The next case consists of giving a typing rule for a basic metavariable (the first premise),
together with a typing rule for a metavariable in the extended derivability structure (and
signature) extended with the basic metavariable that we added.
 -}

data MTypingRule : {Σ : Signature} (E : DerivabilityStructure Σ) (n : ℕ) (k : SyntaxSort) → Set
  where
  []Ty : {Σ : Signature} {E : DerivabilityStructure Σ} → MTypingRule E 0 Ty
  []Tm : {Σ : Signature} {E : DerivabilityStructure Σ} → (t : BMTypingRule E) → MTypingRule E 0 Tm
  _∷_ : {Σ : Signature} {E : DerivabilityStructure Σ} → {n : ℕ} {k : _} (t : BMTypingRule E)
      → MTypingRule (extend E (BMTypingRule-TRule E t) (BMTypingRule-CRule E t)) n k
      → MTypingRule E (suc n) k

{-
If we know how to map to [Σ'] the signature [Σ] extended with a symbol taking [n + 1] arguments,
and that in addition we have a term [a], then we can map to [Σ'] the signature [Σ] extended with
a symbol taking only [n] arguments (putting [a] as the first argument)
-}
extend↑ : {Σ Σ' : Signature} {n m : ℕ} {k : SyntaxSort}
        → Sub (ExtSig Σ (MArity (suc n) k)) Σ' m
        → TmExpr Σ' m
        → Sub (ExtSig Σ (MArity n k)) Σ' m
(extend↑ ↑ a $ (prev s)) x = (↑ $ prev s) x
(extend↑ ↑ a $ new) x = (↑ $ new) (weaken≤ a ∷ x)

{-
Substitution of terms for symbols in typing rules, WIP.
It looks like there is some more refactoring to do. Substituting a term for a symbol in a typing
rule gives a typing rule in a ambient context. So far all of my typing rules are assumed to be in
the empty context, but this cannot be assumed anymore. So we have to change [BMTypingRule] and
[MTypingRule] to be in an ambient context. Not sure how bad this is going to be, but it seems very
reasonable in any case.
-}

BMTypingRule-Subst : {Σ Σ' : Signature} {E : DerivabilityStructure Σ} {m : ℕ}
  → (bt : BMTypingRule E) (a : TmExpr Σ' m)
  → BMTypingRule (extend E (BMTypingRule-TRule E bt) (BMTypingRule-CRule E bt))
  → BMTypingRule E
type (BMTypingRule-Subst bt a t) = {!type t!}
der (BMTypingRule-Subst bt a t) = {!der t!}

MTypingRule-Subst : {Σ Σ' : Signature} {E : DerivabilityStructure Σ} {m : ℕ} {n : ℕ} {k : SyntaxSort}
  → (bt : BMTypingRule E) (a : TmExpr Σ' m)
  → MTypingRule (extend E (BMTypingRule-TRule E bt) (BMTypingRule-CRule E bt)) n k
  → MTypingRule E n k
MTypingRule-Subst bt a []Ty = []Ty
MTypingRule-Subst bt a ([]Tm t) = []Tm (BMTypingRule-Subst bt a t)
MTypingRule-Subst bt a (t ∷ ts) = BMTypingRule-Subst bt a t ∷ MTypingRule-Subst {!BMTypingRule-Subst!} a ts

{-
The derivation rule associated to a typing rule for a metavariable.
For the recursive case, we change the extension of the signature using [extend↑] and we substitute
[a] for the last variable in the typing rule (TODO).
-}
MTypingRule-TRule : {Σ : Signature} (E : DerivabilityStructure Σ) {n : ℕ} {k : SyntaxSort}
                    (t : MTypingRule E n k) {m : ℕ}
                  → DerivationRule (ExtSig Σ (MArity n k)) (MArityJ n k) m
rule (MTypingRule-TRule E []Ty) ↑ Γ = last (◇ ⊢ (↑ $ new) [])
rule (MTypingRule-TRule E ([]Tm t)) ↑ Γ = last (◇ ⊢ (↑ $ new) [] :> ↑Expr (⊂Ext ↑) (weaken^ (type t)))
rule (MTypingRule-TRule E (bt ∷ t)) ↑ Γ =
  next (λ {(◇ ⊢ a :> A) → do
    assume (↑Expr (⊂Ext ↑) (weaken^ (type bt)) ≡ A)
    return (rule (MTypingRule-TRule E (MTypingRule-Subst bt a t)) (extend↑ ↑ a) Γ)})


{- Example, A type and x : A ⊢ B type -}

module _ where
  Σ₀ : Signature
  Symbols Σ₀ _ = Empty  where
    data Empty : Set where

  E₀ = StructuralRules Σ₀

  TypingRuleA : MTypingRule E₀ 0 Ty
  TypingRuleA = []Ty

  E₁ : DerivabilityStructure _
  E₁ = extend E₀ (MTypingRule-TRule E₀ TypingRuleA) {!MTypingRule-CRule E₀ TypingRuleA!}

  TypingRuleB : MTypingRule E₁ 1 Ty
  TypingRuleB = bmtypingrule (sym new []) (apply typingrule (last (◇ ⊢ sym new []))) ∷ []Ty

  E₂ : DerivabilityStructure _
  E₂ = extend E₁ (MTypingRule-TRule E₁ TypingRuleB) {!MTypingRule-CRule E₁ TypingRuleB!}
