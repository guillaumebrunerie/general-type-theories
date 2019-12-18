{-# OPTIONS --prop --rewriting #-}

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
Judgments are indexed by the signature, the length of the context, and most notably by
their sort. Indexing judgments by sorts is very good to get rid of absurd cases, when some
judgments are supposed to have certain sorts.
-}

data Judgment (Σ : Signature) {n : ℕ} (Γ : Ctx Σ n) (m : ℕ) : JudgmentSort → Set where
  _⊢_ : (Δ : DepCtx Σ n m) → TyExpr Σ (n + m) → Judgment Σ Γ m Ty
  _⊢_:>_ : (Δ : DepCtx Σ n m) → TmExpr Σ (n + m) → TyExpr Σ (n + m) → Judgment Σ Γ m Tm
  _⊢_==_ : (Δ : DepCtx Σ n m) → TyExpr Σ (n + m) → TyExpr Σ (n + m) → Judgment Σ Γ m Ty=
  _⊢_==_:>_ : (Δ : DepCtx Σ n m) → TmExpr Σ (n + m) → TmExpr Σ (n + m) → TyExpr Σ (n + m) → Judgment Σ Γ m Tm=


{-
A derivation rule consists of an arity, a size (the length of the context of the conclusion), and of
the rule itself, which is a partial function from tuples of judgments to judgments, everything
being of the right sort and in the correct context-length.
-}

record _⊂_ (Σ Σ' : Signature) : Set where
  constructor make⊂
  field
    _$_ : {n : ℕ} {k : SyntaxSort} → Expr Σ n k → Expr Σ' n k
open _⊂_ public

id⊂ : {Σ : Signature} → Σ ⊂ Σ
id⊂ $ x = x

_∘_ : {Σ Σ' Σ'' : Signature} → Σ' ⊂ Σ'' → Σ ⊂ Σ' → Σ ⊂ Σ''
(g ∘ f) $ x = g $ (f $ x)


{-# NO_UNIVERSE_CHECK #-}
data DerivationRule2 (Σ : Signature) {n : ℕ} (Γ : Ctx Σ n) : (args : JudgmentArityArgs) (kfin : JudgmentSort) → Set where
  last : {k : JudgmentSort} → Judgment Σ Γ 0 k → DerivationRule2 Σ Γ [] k
  next : {m : ℕ} {k kfin : JudgmentSort} {args : JudgmentArityArgs} → (Judgment Σ Γ m k → Partial (DerivationRule2 Σ Γ args kfin)) → DerivationRule2 Σ Γ ((m , k) ∷ args) kfin

record DerivationRule (Σ : Signature) (ar : JudgmentArity) : Set₁ where
  field
    rule : {Σ' : Signature} → Σ ⊂ Σ' → {n : ℕ} (Γ : Ctx Σ' n) → DerivationRule2 Σ' Γ (args ar) (sort ar)
open DerivationRule public

↑DerivationRule : {Σ Σ' : Signature} → Σ ⊂ Σ' → {ar : JudgmentArity} → DerivationRule Σ ar → DerivationRule Σ' ar
rule (↑DerivationRule ↑1 r) ↑2 = rule r (↑2 ∘ ↑1)


{- A derivability structure consists of a bunch of derivation rules -}

record DerivabilityStructure (Σ : Signature) : Set₁ where
  field
    Rules : JudgmentArity → Set
    derivationRule : {ar : JudgmentArity} (r : Rules ar) → DerivationRule Σ ar
open DerivabilityStructure public


{-
A judgment is derivable in a given derivability structure if it can be obtained by applying rules.
So given a rule [r] and a list of judgments [js] that can be applied to it, if the judgments [js]
are all derivable and the rule is defined at [js], then the result of the rule is derivable.

The type [DerivableArgs E js] represents the fact that all of the judgments in [js] are derivable.
-}

module _ {Σ : Signature} {n : ℕ} {Γ : Ctx Σ n} {m : ℕ} {k : JudgmentSort} where

  flattenCtx : Judgment Σ Γ (suc m) k → Ctx Σ (suc n)
  flattenCtx ((X , Δ) ⊢ A)           = (Γ , X)
  flattenCtx ((X , Δ) ⊢ u :> A)      = (Γ , X)
  flattenCtx ((X , Δ) ⊢ A == B)      = (Γ , X)
  flattenCtx ((X , Δ) ⊢ u == v :> A) = (Γ , X)

  flatten : (j : Judgment Σ Γ (suc m) k) → Judgment Σ {n = suc n} (flattenCtx j) m k
  flatten ((X , Δ) ⊢ A)           = Δ ⊢ A
  flatten ((X , Δ) ⊢ u :> A)      = Δ ⊢ u :> A
  flatten ((X , Δ) ⊢ A == B)      = Δ ⊢ A == B
  flatten ((X , Δ) ⊢ u == v :> A) = Δ ⊢ u == v :> A


{- Derivability

[Derivable E j] is true iff the judgment [j] is derivable in [E]. There are two ways a judgment can
be derivable:
- either it is a judgment with a non-trivial dependent context, in which case we simply move the
  types of the dependent context to the normal context
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

{-# NO_UNIVERSE_CHECK #-}
data Apply {Σ : Signature} (E : DerivabilityStructure Σ)
           {n : ℕ} {Γ : Ctx Σ n} {k : JudgmentSort}
           : {ar : JudgmentArityArgs} → DerivationRule2 Σ Γ ar k → Judgment Σ Γ 0 k → Prop where
  last : (j : Judgment Σ Γ 0 k) → Apply E (last j) j
  next : {m : ℕ} {ar : _} (f : Judgment Σ Γ m k → Partial (DerivationRule2 Σ Γ ar k)) (jj : Judgment Σ Γ 0 k) (j : Judgment Σ Γ m k)
       → (def : isDefined (f j))
       → Derivable E j
       → Apply E (f j $ def) jj
       → Apply E (next f) jj

data Derivable {Σ} E where
  apply : {n : ℕ} {Γ : Ctx Σ n} {k : JudgmentSort} {j : Judgment Σ Γ 0 k}
          {args : JudgmentArityArgs} (r : Rules E (mkarity args k))
          → Apply E (rule (derivationRule E r) id⊂ Γ) j
          → Derivable E j
  flat : {n : ℕ} {Γ : Ctx Σ n} {m : ℕ} {k : JudgmentSort} {j : Judgment Σ Γ (suc m) k} → Derivable E (flatten j) → Derivable E j


{- We now define the structural rules -}

module _ (Σ : Signature) where

  VarRule : (n : ℕ) → DerivationRule Σ (mkarity ((0 , Ty) ∷ []) Tm)
  rule (VarRule k) ↑ Γ =
    (next (λ {(◇ ⊢ A) → do
       (k' , A') ← get k Γ
       assume (A' ≡ A)
       return (last (◇ ⊢ var k' :> A))}))

  TyReflRule : DerivationRule Σ (mkarity ((0 , Ty) ∷ []) Ty=)
  rule TyReflRule ↑ Γ = next (λ {(◇ ⊢ A) → return (last (◇ ⊢ A == A))})

  {-
  This one and the next one could be simplified, I just wanted to check that the full version is
  still doable
  -}

  TySymmRule : DerivationRule Σ (mkarity ((0 , Ty) ∷ (0 , Ty) ∷ (0 , Ty=) ∷ []) Ty=)
  rule TySymmRule ↑ Γ =
    (next (λ {(◇ ⊢ A) → return
    (next (λ {(◇ ⊢ B) → return
    (next (λ {(◇ ⊢ A' == B') → do
      assume (A ≡ A')
      assume (B ≡ B')
      return (last (◇ ⊢ B' == A'))}))}))}))

--   -- TODO
--   TyTranRule : DerivationRule Σ (mkarity ((0 , Ty) ∷ (0 , Ty) ∷ (0 , Ty) ∷ (0 , Ty=) ∷ (0 , Ty=) ∷ []) Ty=)
--   rule TyTranRule ↑ Γ₀ ((Γ'''' ⊢ A') ∷ (Γ''' ⊢ B'') ∷ (Γ'' ⊢ C')
--                        ∷ (Γ ⊢ A == B) ∷ (Γ' ⊢ B' == C) ∷ []) =
--     do
--       assume (Γ ≡ Γ')
--       assume (Γ' ≡ Γ'')
--       assume (Γ'' ≡ Γ''')
--       assume (Γ''' ≡ Γ'''')
--       assume (A ≡ A')
--       assume (B ≡ B')
--       assume (B' ≡ B'')
--       assume (C ≡ C')
--       return (Γ ⊢ A == C)

  ConvRule : DerivationRule Σ (mkarity ((0 , Tm) ∷ (0 , Ty=) ∷ []) Tm)
  rule ConvRule ↑ Γ =
    (next (λ { (◇ ⊢ u :> A) → return
    (next (λ { (◇ ⊢ A' == B) → do
      assume (A ≡ A')
      return
       (last (◇ ⊢ u :> B))}))}))

  ConvEqRule : DerivationRule Σ (mkarity ((0 , Tm=) ∷ (0 , Ty=) ∷ []) Tm=)
  rule ConvEqRule ↑ Γ =
    (next (λ { (◇ ⊢ u == v :> A) → return
    (next (λ { (◇ ⊢ A' == B) → do
      assume (A ≡ A')
      return
       (last (◇ ⊢ u == v :> B))}))}))

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
    -- tyTran : StructuralRulesType
    -- tmRefl : StructuralRulesType
    -- tmSymm : StructuralRulesType
    -- tmTran : StructuralRulesType

  Rules StructuralRules ar = StructuralRulesType {ar}
  derivationRule StructuralRules (var k) = VarRule k
  derivationRule StructuralRules conv = ConvRule
  derivationRule StructuralRules convEq = ConvEqRule
  derivationRule StructuralRules tyRefl = TyReflRule
  derivationRule StructuralRules tySymm = TySymmRule
  -- derivationRule StructuralRules tyTran = {!TyTranRule!}
  -- derivationRule StructuralRules tmRefl = {!TmReflRule!}
  -- derivationRule StructuralRules tmSymm = {!TmSymmRule!}
  -- derivationRule StructuralRules tmTran = {!TmTranRule!}


{- Typing rules for basic metavariables -}

record BMTypingRule {Σ : Signature} (E : DerivabilityStructure Σ) : Set where
  constructor bmtypingrule
  field
    type : TyExpr Σ 0
    der : Derivable E {Γ = ◇} (◇ ⊢ type)
open BMTypingRule public

{- Arities for the symbols and the rules corresponding to basic metavariables -}

BMArity : SyntaxArity
args BMArity = []
sort BMArity = Tm

BMArityJ : JudgmentArity
args BMArityJ = []
sort BMArityJ = Tm

BMArityJ= : JudgmentArity
args BMArityJ= = []
sort BMArityJ= = Tm=

BMSymbols : Signature → Set
BMSymbols Σ = Symbols Σ BMArity

{-
Given a symbol (already in the signature) which has the arity of a basic metavariable and a typing
rule, we define two derivation rules (typing rule and congruence rule).
Those derivation rules are actually parametrized by the context, so we have ((n : ℕ) × Ctx Σ n)-many
derivation rules in both cases.
-}

↑Args : {Σ Σ' : Signature} (↑ : Σ ⊂ Σ') {n : ℕ} {ar : SyntaxArityArgs} → generateArgs Σ n ar → generateArgs Σ' n ar
↑Args ↑ [] = []
↑Args ↑ (x ∷ l) = (↑ $ x) ∷ ↑Args ↑ l

↑Ctx : {Σ Σ' : Signature} (↑ : Σ ⊂ Σ') {n : ℕ} → Ctx Σ n → Ctx Σ' n
↑Ctx ↑ ◇ = ◇
↑Ctx ↑ (Γ , A) = (↑Ctx ↑ Γ , ↑ $ A)


{-
Given a type [A] representing typing rules, the type [Ext A] represents the typing rule when we
have added those for a new symbol, and [extend E t c] does the extension.
Note: shouldn’t we extend the signature as well?
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

ExtSig : Signature → SyntaxArity → Signature
Symbols (ExtSig Σ ar) = ExtSigSymbols  module _ where

  data ExtSigSymbols : SyntaxArity → Set where
    prev : {ar0 : SyntaxArity} → Symbols Σ ar0 → ExtSigSymbols ar0
    new : ExtSigSymbols ar

⊂Ext0 : {Σ : Signature} {ar : SyntaxArity} → Σ ⊂ ExtSig Σ ar
⊂Ext1 : {Σ : Signature} {n : ℕ} {ar : SyntaxArity} {args : SyntaxArityArgs} → generateArgs Σ n args → generateArgs (ExtSig Σ ar) n args

⊂Ext0 $ var x = var x
⊂Ext0 $ sym s x = sym (prev s) (⊂Ext1 x)

⊂Ext1 [] = []
⊂Ext1 (e ∷ es) = (⊂Ext0 $ e) ∷ ⊂Ext1 es

⊂Ext : {Σ Σ' : Signature} {ar : SyntaxArity} → ExtSig Σ ar ⊂ Σ' → Σ ⊂ Σ'
⊂Ext ↑ = ↑ ∘ ⊂Ext0

extend : {Σ : Signature} (E : DerivabilityStructure Σ)
         {ar : SyntaxArity}
         (t : DerivationRule (ExtSig Σ ar) (TArity ar))
         (c : DerivationRule (ExtSig Σ ar) (CArity ar))
         → DerivabilityStructure (ExtSig Σ ar)
Rules (extend E {ar} t c) = Ext (Rules E) ar  module _ where

  data Ext (A : JudgmentArity → Set) (arnew : SyntaxArity) : JudgmentArity → Set where
    prev : {ar : JudgmentArity} → A ar → Ext A arnew ar
    typingrule : Ext A arnew (TArity arnew)
    congruencerule : Ext A arnew (CArity arnew)

derivationRule (extend E t c) (prev r) = ↑DerivationRule (⊂Ext id⊂) (derivationRule E r)
derivationRule (extend E t c) typingrule = t
derivationRule (extend E t c) congruencerule = c


extend₀ : {Σ : Signature} (E : DerivabilityStructure Σ)
         {ar : SyntaxArity}
         → DerivabilityStructure (ExtSig Σ ar)
Rules (extend₀ E) = Rules E
derivationRule (extend₀ E) r = ↑DerivationRule (⊂Ext id⊂) (derivationRule E r)

BMTypingRule-TRule : {Σ : Signature} (E : DerivabilityStructure Σ)
                     (t : BMTypingRule E)
                     → DerivationRule (ExtSig Σ BMArity) BMArityJ
rule (BMTypingRule-TRule E t) ↑ Γ = last (◇ ⊢ (↑ $ sym new []) :> ((⊂Ext ↑) $ weaken^ (type t)))

BMTypingRule-CRule : {Σ : Signature} (E : DerivabilityStructure Σ)
                     (t : BMTypingRule E)
                     → DerivationRule (ExtSig Σ BMArity) BMArityJ=
rule (BMTypingRule-CRule E t) ↑ Γ = last (◇ ⊢ (↑ $ sym new []) == (↑ $ sym new []) :> ((⊂Ext ↑) $ weaken^ (type t)))

{- Arity (and arityArgs) of a metavariable -}

MArityArgs : ℕ → SyntaxArityArgs
MArityArgs zero = []
MArityArgs (suc n) = (0 , Tm) ∷ MArityArgs n

MArity : ℕ → SyntaxSort → SyntaxArity
args (MArity n k) = MArityArgs n
sort (MArity n k) = k

MSymbols : Signature → ℕ → SyntaxSort → Set
MSymbols Σ n k = Symbols Σ (MArity n k)

{- Typing rules for metavariables -}

data MTypingRule : {Σ : Signature} (E : DerivabilityStructure Σ) (n : ℕ) (k : SyntaxSort) → Set
  where
  []Ty : {Σ : Signature} {E : DerivabilityStructure Σ} → MTypingRule E 0 Ty
  []Tm : {Σ : Signature} {E : DerivabilityStructure Σ} → (type : TyExpr Σ 0) (der : Derivable E {Γ = ◇} (◇ ⊢ type)) → MTypingRule E 0 Tm
  _∷_ : {Σ : Signature} {E : DerivabilityStructure Σ} → {n : ℕ} {k : _} (t : BMTypingRule E)
      → MTypingRule (extend E (BMTypingRule-TRule E t) (BMTypingRule-CRule E t)) n k
      → MTypingRule E (suc n) k

[0,Tm]^J : ℕ → JudgmentArityArgs
[0,Tm]^J zero = []
[0,Tm]^J (suc n) = (0 , Tm) ∷ [0,Tm]^J n

extend↑ : {Σ Σ' : Signature} {n : ℕ} {k : SyntaxSort} → TmExpr Σ' {!!} → ExtSig Σ (MArity (suc n) k) ⊂ Σ' → ExtSig Σ (MArity n k) ⊂ Σ'
extend↑2 : {Σ Σ' : Signature} {n m : ℕ} {k : SyntaxSort} {args : SyntaxArityArgs} → TmExpr Σ' {!!} → generateArgs (ExtSig Σ (MArity n k)) m args → generateArgs (ExtSig Σ (MArity (suc n) k)) m args

extend↑ a ↑ $ var k = var k
extend↑ a ↑ $ sym (prev s) x = {!↑ $ (sym (prev s) {!(extend↑2 a x)!})!}
extend↑ a ↑ $ sym new x = {!sym new ({!⊂Ext0 $ (weaken^ a)!} ∷ extend↑2 ↑ a x)!}

extend↑2 a [] = []
extend↑2 a (e ∷ es) = {!(extend↑ ↑ a $ e) ∷ extend↑2 ↑ a es!}

MTypingRule-TRule : {Σ : Signature} (E : DerivabilityStructure Σ) {n : ℕ} {k : SyntaxSort}
                    (t : MTypingRule E n k)
                  → DerivationRule (ExtSig Σ (MArity n k)) (mkarity ([0,Tm]^J n) (SStoJS k))
rule (MTypingRule-TRule E []Ty) ↑ Γ = last (◇ ⊢ (↑ $ (sym new [])))
rule (MTypingRule-TRule E ([]Tm T _)) ↑ Γ = last (◇ ⊢ (↑ $ (sym new [])) :> ((⊂Ext ↑) $ weaken^ T))
rule (MTypingRule-TRule E (bt ∷ t)) ↑ Γ =
  next (λ {(◇ ⊢ a :> A) → do
    assume {!type bt == A!}
    return (rule (MTypingRule-TRule E {!substitution a / s in t!}) (↑ ∘ extend↑ {!↑!} {!!}) Γ)})
-- rule (MTypingRule-TRule E []Ty) ↑ Γ [] = return (Γ ⊢ (sym (↑ $ new) []))
-- rule (MTypingRule-TRule E ([]Tm type der)) ↑ Γ [] = return (Γ ⊢ sym (↑ $ new) [] :> ↑Expr ↑ (↑Expr ⊂Ext (weaken^ type)))
-- rule (MTypingRule-TRule E (bt ∷ t)) ↑ Γ (Γ' ⊢ a :> T ∷ js) = do
--   assume {!type bt!}
--   rule (MTypingRule-TRule E {!!}) ↑ Γ {!!}


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
  E₂ = extend E₁ (MTypingRule-TRule E₁ TypingRuleB) {!!}
