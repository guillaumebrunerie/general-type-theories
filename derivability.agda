{-# OPTIONS --prop #-}

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

data Judgment (Σ : Signature) (n : ℕ) : JudgmentSort → Set where
  _⊢_ : (Γ : Ctx Σ n) → TyExpr Σ n → Judgment Σ n Ty
  _⊢_:>_ : (Γ : Ctx Σ n) → TmExpr Σ n → TyExpr Σ n → Judgment Σ n Tm
  _⊢_==_ : (Γ : Ctx Σ n) → TyExpr Σ n → TyExpr Σ n → Judgment Σ n Ty=
  _⊢_==_:>_ : (Γ : Ctx Σ n) → TmExpr Σ n → TmExpr Σ n → TyExpr Σ n → Judgment Σ n Tm=


{-
A derivation rule consists of an arity, a size (the length of the context of the conclusion), and of
the rule itself, which is a partial function from tuples of judgments to judgments, everything
being of the right sort and in the correct context-length.
-}

data DerivationRulePremises (Σ : Signature) (n : ℕ) : JudgmentArityArgs → Set where
  [] : DerivationRulePremises Σ n []
  _∷_ : {m : ℕ} {k : JudgmentSort} {args : JudgmentArityArgs} → Judgment Σ (m + n) k
      → DerivationRulePremises Σ n args → DerivationRulePremises Σ n ((m , k) ∷ args)

record _⊂_ (Σ Σ' : Signature) : Set where
  constructor make⊂
  field
    _$_ : {ar : SyntaxArity} → Symbols Σ ar → Symbols Σ' ar
open _⊂_ public

id⊂ : {Σ : Signature} → Σ ⊂ Σ
id⊂ $ x = x

_∘_ : {Σ Σ' Σ'' : Signature} → Σ' ⊂ Σ'' → Σ ⊂ Σ' → Σ ⊂ Σ''
(g ∘ f) $ x = g $ (f $ x)

record DerivationRule (Σ : Signature) (ar : JudgmentArity) : Set₁ where
  field
    rule : {Σ' : Signature} → Σ ⊂ Σ' → {n : ℕ} → Ctx Σ' n → DerivationRulePremises Σ' n (args ar) → Partial (Judgment Σ' n (sort ar))
open DerivationRule public

↑DerivationRule : {Σ Σ' : Signature} → Σ ⊂ Σ' → {ar : JudgmentArity} → DerivationRule Σ ar → DerivationRule Σ' ar
DerivationRule.rule (↑DerivationRule f record { rule = rule }) g = rule (g ∘ f)

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

The type [DerivableArgs E js] represents the fact that all of the judgments is [js] are derivables.
-}

data Derivable {Σ : Signature} (E : DerivabilityStructure Σ)
     : {n : ℕ} {k : JudgmentSort} → Judgment Σ n k → Prop

data DerivableArgs {Σ : Signature} (E : DerivabilityStructure Σ) {n : ℕ}
     : {ar : JudgmentArityArgs} → DerivationRulePremises Σ n ar → Prop where
  []  : DerivableArgs E []
  _∷_ : {m : ℕ} {k : JudgmentSort} {j : Judgment Σ (m + n) k}
        {ar : JudgmentArityArgs} {js : DerivationRulePremises Σ n ar}
        → Derivable E j → DerivableArgs E js
        → DerivableArgs E (j ∷ js)

data Derivable {Σ} E where
  apply : {ar : JudgmentArity} (r : Rules E ar) {n : ℕ} {js : DerivationRulePremises Σ n (args ar)}
          (js-der : DerivableArgs E js) (Γ : Ctx Σ n) (def : isDefined (rule (derivationRule E r) id⊂ Γ js))
          → Derivable E (rule (derivationRule E r) id⊂ Γ js $ def)

{- We now define the structural rules -}

module _ (Σ : Signature) where

  -- VarRule : {n : ℕ} → VarPos n → DerivationRule Σ (mkarity ((0 , Ty) ∷ []) Tm)
  -- rule (VarRule k) ↑ Γ (Γ' ⊢ A ∷ []) =
  --   do
  --     assume (Γ ≡ Γ')
  --     assume (get k Γ ≡ A)
  --     return (Γ' ⊢ var k :> A)

  TyReflRule : DerivationRule Σ (mkarity ((0 , Ty) ∷ []) Ty=)
  rule TyReflRule ↑ Γ' ((Γ ⊢ A) ∷ []) =
    do
      assume (Γ ≡ Γ')
      return (Γ ⊢ A == A)

  {-
  This one and the next one could be simplified, I just wanted to check that the full version is
  still doable
  -}

  TySymmRule : DerivationRule Σ (mkarity ((0 , Ty) ∷ (0 , Ty) ∷ (0 , Ty=) ∷ []) Ty=)
  rule TySymmRule ↑ Γ₀ ((Γ'' ⊢ A') ∷ (Γ' ⊢ B') ∷ (Γ ⊢ A == B) ∷ []) =
    do
      assume (Γ ≡ Γ')
      assume (Γ' ≡ Γ)
      assume (A ≡ A')
      assume (B ≡ B')
      return (Γ ⊢ B == A)

  TyTranRule : DerivationRule Σ (mkarity ((0 , Ty) ∷ (0 , Ty) ∷ (0 , Ty) ∷ (0 , Ty=) ∷ (0 , Ty=) ∷ []) Ty=)
  rule TyTranRule ↑ Γ₀ ((Γ'''' ⊢ A') ∷ (Γ''' ⊢ B'') ∷ (Γ'' ⊢ C')
                       ∷ (Γ ⊢ A == B) ∷ (Γ' ⊢ B' == C) ∷ []) =
    do
      assume (Γ ≡ Γ')
      assume (Γ' ≡ Γ'')
      assume (Γ'' ≡ Γ''')
      assume (Γ''' ≡ Γ'''')
      assume (A ≡ A')
      assume (B ≡ B')
      assume (B' ≡ B'')
      assume (C ≡ C')
      return (Γ ⊢ A == C)

  ConvRule : DerivationRule Σ (mkarity ((0 , Tm) ∷ (0 , Ty=) ∷ []) Tm)
  rule ConvRule ↑ Γ₀ ((Γ ⊢ u :> A) ∷ ((Γ' ⊢ A' == B) ∷ [])) =
    do
      assume (Γ ≡ Γ')
      assume (A ≡ A')
      return (Γ ⊢ u :> B)

  StructuralRules : DerivabilityStructure Σ

  data StructuralRulesType : JudgmentArity → Set where
--    var : (k : VarPos n) → StructuralRulesType _
    tyRefl : StructuralRulesType _
    tySymm : StructuralRulesType _
    tyTran : StructuralRulesType _
    conv : StructuralRulesType _
    TODO : StructuralRulesType (mkarity [] Ty)
    
  Rules StructuralRules = StructuralRulesType
--  derivationRule StructuralRules (var k) = VarRule k
  derivationRule StructuralRules tyRefl = TyReflRule
  derivationRule StructuralRules tySymm = TySymmRule
  derivationRule StructuralRules tyTran = TyTranRule
  derivationRule StructuralRules conv = ConvRule
  derivationRule StructuralRules TODO = {!!}


{- Typing rules for basic metavariables -}

record BMTypingRule {Σ : Signature} (E : DerivabilityStructure Σ) : Set where
  constructor bmtypingrule
  field
    type : TyExpr Σ 0
    der : Derivable E (◇ ⊢ type)
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

↑Expr : {Σ Σ' : Signature} (↑ : Σ ⊂ Σ') {n : ℕ} {k : SyntaxSort} → Expr Σ n k → Expr Σ' n k
↑Args : {Σ Σ' : Signature} (↑ : Σ ⊂ Σ') {n : ℕ} {ar : SyntaxArityArgs} → generateArgs Σ n ar → generateArgs Σ' n ar

↑Expr ↑ (var x) = var x
↑Expr (make⊂ ↑) (sym s x) = sym (↑ s) (↑Args (make⊂ ↑) x)

↑Args ↑ [] = []
↑Args ↑ (x ∷ l) = ↑Expr ↑ x ∷ ↑Args ↑ l

↑Ctx : {Σ Σ' : Signature} (↑ : Σ ⊂ Σ') {n : ℕ} → Ctx Σ n → Ctx Σ' n
↑Ctx ↑ ◇ = ◇
↑Ctx ↑ (Γ , A) = (↑Ctx ↑ Γ , ↑Expr ↑ A)


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

⊂Ext : {Σ : Signature} {ar : SyntaxArity} → Σ ⊂ ExtSig Σ ar
⊂Ext = make⊂ prev

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

derivationRule (extend E t c) (prev r) = ↑DerivationRule ⊂Ext (derivationRule E r)
derivationRule (extend E t c) typingrule = t
derivationRule (extend E t c) congruencerule = c


extend₀ : {Σ : Signature} (E : DerivabilityStructure Σ)
         {ar : SyntaxArity}
         → DerivabilityStructure (ExtSig Σ ar)
Rules (extend₀ E) = Rules E
derivationRule (extend₀ E) r = ↑DerivationRule ⊂Ext (derivationRule E r)

BMTypingRule-TRule : {Σ : Signature} (E : DerivabilityStructure Σ)
                     (t : BMTypingRule E)
                     → DerivationRule (ExtSig Σ BMArity) BMArityJ
rule (BMTypingRule-TRule E t) ↑ Γ [] = return (Γ ⊢ sym (↑ $ new) [] :> weaken^ (↑Expr ↑ (↑Expr ⊂Ext (type t))))

BMTypingRule-CRule : {Σ : Signature} (E : DerivabilityStructure Σ)
                     (t : BMTypingRule E)
                     → DerivationRule (ExtSig Σ BMArity) BMArityJ=
rule (BMTypingRule-CRule E t) ↑ Γ [] = return (Γ ⊢ sym (↑ $ new) [] == sym (↑ $ new) [] :> weaken^ (↑Expr ↑ (↑Expr ⊂Ext (type t))))

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
  []Tm : {Σ : Signature} {E : DerivabilityStructure Σ} → (type : TyExpr Σ 0) (der : Derivable E (◇ ⊢ type)) → MTypingRule E 0 Tm
  _∷_ : {Σ : Signature} {E : DerivabilityStructure Σ} → {n : ℕ} {k : _} (t : BMTypingRule E)
      → MTypingRule (extend E (BMTypingRule-TRule E t) (BMTypingRule-CRule E t)) n k
      → MTypingRule E (suc n) k

[0,Tm]^J : ℕ → JudgmentArityArgs
[0,Tm]^J zero = []
[0,Tm]^J (suc n) = (0 , Tm) ∷ [0,Tm]^J n

MTypingRule-TRule : {Σ : Signature} (E : DerivabilityStructure Σ) {n : ℕ} {k : SyntaxSort}
                    (t : MTypingRule E n k)
                  → DerivationRule (ExtSig Σ (MArity n k)) (mkarity ([0,Tm]^J n) (SStoJS k))
rule (MTypingRule-TRule E []Ty) ↑ Γ [] = return (Γ ⊢ (sym (↑ $ new) []))
rule (MTypingRule-TRule E ([]Tm type der)) ↑ Γ [] = return (Γ ⊢ sym (↑ $ new) [] :> ↑Expr ↑ (↑Expr ⊂Ext (weaken^ type)))
rule (MTypingRule-TRule E (bt ∷ t)) ↑ Γ (j ∷ js) = {!where things happen!}


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
  TypingRuleB = bmtypingrule (sym new []) (apply typingrule [] ◇ tt) ∷ []Ty

  E₂ : DerivabilityStructure _
  E₂ = extend E₁ (MTypingRule-TRule E₁ TypingRuleB) {!!}
