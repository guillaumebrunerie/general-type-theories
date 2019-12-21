{-# OPTIONS --rewriting --prop --allow-unsolved-metas #-}

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
  _⊢_       : (Δ : DepCtx Σ m n) → TyExpr Σ (n + m) → Judgment Σ Γ n Ty
  _⊢_:>_    : (Δ : DepCtx Σ m n) → TmExpr Σ (n + m) → TyExpr Σ (n + m) → Judgment Σ Γ n Tm
  _⊢_==_    : (Δ : DepCtx Σ m n) → TyExpr Σ (n + m) → TyExpr Σ (n + m) → Judgment Σ Γ n Ty=
  _⊢_==_:>_ : (Δ : DepCtx Σ m n) → TmExpr Σ (n + m) → TmExpr Σ (n + m) → TyExpr Σ (n + m)
            → Judgment Σ Γ n Tm=


{-
In order to deal with extensions of signatures, we need a notion of map between signatures. There
are a few possible options:
- Mapping symbols to symbols: not strong enough, as later we need to map a symbol s(-) to the
  expression s(a, -)
- Mapping expressions to expressions: too strong, makes it impossible to look inside expressions
- Mapping symbols to expression-building function: this is the approach we take. A symbol will be
  mapped to a function of the corresponding arity between expressions of the codomain signature.

We need sometimes to restrict them to expressions in a certain scope (bounded below). This happens
for instance when turning typing rules to partial functions on the syntax, we replace something by a
specific term which lives in a scope, so the map between signatures does not work for a lower scope.
We need to have it bounded below (as opposed to having a fixed scope) otherwise we cannot map
expressions to expressions (asthey may bind new variables).

Therefore we define [Sub Σ Σ' n] which represents maps from symbols of [Σ] to expression-building
functions for signature [Σ'], and which works for any scope above (and including) [n].
-}

record Sub (Σ Σ' : Signature) (n : ℕ) : Set where
  constructor sub
  field
    _$_ : {m : ℕ} {{p : n ≤ m}} {ar : SyntaxArity} (s : Symbols Σ ar) → Args Σ' m (args ar) → Expr Σ' m (sort ar)
open Sub public

{- Identity map -}

id⊂ : {n : ℕ} {Σ : Signature} → Sub Σ Σ n
id⊂ $ s = sym s

{- Lifting at a higher scope -}

liftSub : {n m : ℕ} {Σ Σ' : Signature} {{p : n ≤ m}} → Sub Σ Σ' n → Sub Σ Σ' m
(liftSub ↑ $ s) x = (↑ $ s) x

{- Lifting of a map between signatures to expressions -}

↑Expr : {Σ Σ' : Signature} {n : ℕ} {k : SyntaxSort} → Sub Σ Σ' n → Expr Σ n k → Expr Σ' n k
↑Args : {Σ Σ' : Signature} {n : ℕ} {args : SyntaxArityArgs} → Sub Σ Σ' n → Args Σ n args → Args Σ' n args

↑Expr ↑ (var x) = var x
↑Expr ↑ (sym s x) = (↑ $ s) (↑Args ↑ x)

↑Args ↑ [] = []
↑Args ↑ (es , e) = ↑Args ↑ es , ↑Expr (liftSub ↑) e


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

record DerivationRule (Σ : Signature) (ar : JudgmentArity) (n : ℕ) : Set₁ where
  field
    rule : {Σ' : Signature} → Sub Σ Σ' n → (Γ : Ctx Σ' n)
         → DerivationRulePremises Σ' Γ (args ar) → Partial (Judgment Σ' Γ 0 (sort ar))
open DerivationRule public

{- A derivability structure consists of a bunch of derivation rules, indexed by their arities -}

record DerivabilityStructure (Σ : Signature) : Set₁ where
  field
    Rules : JudgmentArity → Set
    derivationRule : {ar : JudgmentArity} (r : Rules ar) {n : ℕ} → DerivationRule Σ ar n
open DerivabilityStructure public


{- We can move the local context to the end of the ambient context -}

module _ {Σ : Signature} {m : ℕ} {Γ : Ctx Σ m} where

  Γ+_ : {l : ℕ} (Δ : DepCtx Σ m l) → Ctx Σ (l + m)
  Γ+ ◇ = Γ
  Γ+ (Δ , A) = (Γ+ Δ , A)

  exchangeCtx : {n : ℕ} {k : JudgmentSort} → Judgment Σ Γ n k → Ctx Σ (n + m)
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
A judgment can be derivable in two different ways:
- if it has a non-trivial local context, then we just move the local context to the end of the
  ambient context and try again,
- if it has a trivial local context, then it should be obtained by applying a rule [r] from the
  derivability structure to a list of judgments [js] which are all derivable [js-der] and for which
  the rule is defined [def].

The type [DerivableArgs E js] represents the fact that all of the judgments in [js] are derivables.
The type [Derivable E j] represents the fact that the judgment [j] is derivable.
-}

data Derivable {Σ : Signature} (E : DerivabilityStructure Σ)
     : {m : ℕ} {Γ : Ctx Σ m} {n : ℕ} {k : JudgmentSort} → Judgment Σ Γ n k → Prop

data DerivableArgs {Σ : Signature} (E : DerivabilityStructure Σ) {m : ℕ} {Γ : Ctx Σ m}
     : {ar : JudgmentArityArgs} → DerivationRulePremises Σ Γ ar → Prop where
  []  : DerivableArgs E []
  _,_ : {n : ℕ} {k : JudgmentSort} {j : Judgment Σ Γ n k}
        {ar : JudgmentArityArgs} {js : DerivationRulePremises Σ Γ ar}
        → DerivableArgs E js
        → Derivable E j
        → DerivableArgs E (js , j)

data Derivable {Σ} E where
  apply : {ar : JudgmentArity} (r : Rules E ar) {m : ℕ} {Γ : Ctx Σ m} {js : DerivationRulePremises Σ Γ (args ar)}
          (js-der : DerivableArgs E js) {{def : isDefined (rule (derivationRule E r) id⊂ Γ js)}}
          → Derivable E (rule (derivationRule E r) id⊂ Γ js $ def)
  flat : {m : ℕ} {Γ : Ctx Σ m} {n : ℕ} {k : JudgmentSort} {j : Judgment Σ Γ (suc n) k} → Derivable E (exchange j) → Derivable E j


{- We now define the structural rules -}

module _ (Σ : Signature) where

  VarRule : (k : ℕ) {n : ℕ} → DerivationRule Σ (mkarity ([] , (0 , Ty)) Tm) n
  rule (VarRule k) ↑ Γ ([] , ◇ ⊢ A) =
    do
      (k' , A') ← get k Γ
      assume (A' ≡ A)
      return (◇ ⊢ var k' :> A)

  ConvRule : {n : ℕ} → DerivationRule Σ (mkarity ([] , (0 , Tm) , (0 , Ty=)) Tm) n
  rule ConvRule ↑ Γ ([] , ◇ ⊢ u :> A , ◇ ⊢ A' == B) =
    do
      assume (A ≡ A')
      return (◇ ⊢ u :> B)

  ConvEqRule : {n : ℕ} → DerivationRule Σ (mkarity ([] , (0 , Tm=) , (0 , Ty=)) Tm=) n
  rule ConvEqRule ↑ Γ ([] , ◇ ⊢ u == v :> A , ◇ ⊢ A' == B) =
    do
      assume (A ≡ A')
      return (◇ ⊢ u == v :> B)

  TyReflRule : {n : ℕ} → DerivationRule Σ (mkarity ([] , (0 , Ty)) Ty=) n
  rule TyReflRule ↑ Γ ([] , ◇ ⊢ A) = return (◇ ⊢ A == A)

  {-
  This one and the next one could be simplified, I just wanted to check that the full version is
  still doable
  -}

  TySymmRule : {n : ℕ} → DerivationRule Σ (mkarity ([] , (0 , Ty) , (0 , Ty) , (0 , Ty=)) Ty=) n
  rule TySymmRule ↑ Γ ([] , (◇ ⊢ A') , (◇ ⊢ B') , ◇ ⊢ A == B) =
    do
      assume (A ≡ A')
      assume (B ≡ B')
      return (◇ ⊢ B == A)

  TyTranRule : {n : ℕ} → DerivationRule Σ (mkarity ([] , (0 , Ty) , (0 , Ty) , (0 , Ty) , (0 , Ty=) , (0 , Ty=)) Ty=) n
  rule TyTranRule ↑ Γ ([] , (◇ ⊢ A') , (◇ ⊢ B') , (◇ ⊢ C') , ◇ ⊢ A == B , ◇ ⊢ B'' == C) =
    do
      assume (A ≡ A')
      assume (B ≡ B')
      assume (B' ≡ B'')
      assume (C ≡ C')
      return (◇ ⊢ A == C)


  TmReflRule : {n : ℕ} → DerivationRule Σ (mkarity ([] , (0 , Tm)) Tm=) n
  rule TmReflRule ↑ Γ ([] , ◇ ⊢ u :> A) = return (◇ ⊢ u == u :> A)

  TmSymmRule : {n : ℕ} → DerivationRule Σ (mkarity ([] , (0 , Tm=)) Tm=) n
  rule TmSymmRule ↑ Γ ([] , ◇ ⊢ u == v :> A) = return (◇ ⊢ v == u :> A)

  TmTranRule : {n : ℕ} → DerivationRule Σ (mkarity ([] , (0 , Tm=) , (0 , Tm=)) Tm=) n
  rule TmTranRule ↑ Γ ([] , ◇ ⊢ u == v :> A , ◇ ⊢ v' == w :> A') =
    do
      assume (v ≡ v')
      assume (A ≡ A')
      return (◇ ⊢ u == w :> A)

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


{- Helper functions to compute the arity of a rule given the arity of the symbol. -}

SStoJS : SyntaxSort → JudgmentSort
SStoJS Ty = Ty
SStoJS Tm = Tm

SStoJS= : SyntaxSort → JudgmentSort
SStoJS= Ty = Ty=
SStoJS= Tm = Tm=

TArityArgs : SyntaxArityArgs → JudgmentArityArgs
TArityArgs [] = []
TArityArgs (ar , (n , k)) = TArityArgs ar , (n , SStoJS k)

TArity : SyntaxArity → JudgmentArity
TArity ar = mkarity (TArityArgs (args ar)) (SStoJS (sort ar))

CArityArgs : SyntaxArityArgs → JudgmentArityArgs
CArityArgs [] = []
CArityArgs (ar , (n , k)) = CArityArgs ar , (n , SStoJS= k)

CArity : SyntaxArity → JudgmentArity
CArity ar = mkarity (CArityArgs (args ar)) (SStoJS= (sort ar))

{-
[ExtSig Σ ar] extends the signature [Σ] by an arity [ar].
In order to add a symbol only at the correct arity, we use an inductive family (another possibility
would be to use decidable equality on the symbols but that would be very ugly).
-}

data ExtSigSymbols (S : SyntaxArity → Set) (ar : SyntaxArity) : SyntaxArity → Set where
  prev : {ar' : SyntaxArity} → S ar' → ExtSigSymbols S ar ar'
  new : ExtSigSymbols S ar ar

ExtSig : Signature → SyntaxArity → Signature
Symbols (ExtSig Σ ar) = ExtSigSymbols (Symbols Σ) ar

{- If an extended signature maps to [Σ'], then the original signature too. -}
⊂Ext : {Σ Σ' : Signature} {ar : SyntaxArity} {n : ℕ} → Sub (ExtSig Σ ar) Σ' n → Sub Σ Σ' n
⊂Ext ↑ $ s = ↑ $ (prev s)

{-
[↑DerivationRule r] extends the derivation rule [r] to an extended signature.
This is easy because derivation rules were designed to be extendable.
-}
↑DerivationRule : {Σ : Signature} {ar : SyntaxArity} {ar' : JudgmentArity} {n : ℕ}
                → DerivationRule Σ ar' n → DerivationRule (ExtSig Σ ar) ar' n
rule (↑DerivationRule r) ↑ Γ = rule r (⊂Ext ↑) Γ

{- Record combining the typing and congruence rules for a new symbol. -}
record DerivationRules (Σ : Signature) (ar : SyntaxArity) (l : ℕ) : Set₁ where
  field
    typingdrule     : {m : ℕ} {{p : l ≤ m}} → DerivationRule (ExtSig Σ ar) (TArity ar) m
    congruencedrule : {m : ℕ} {{p : l ≤ m}} → DerivationRule (ExtSig Σ ar) (CArity ar) m
open DerivationRules public

{-
[extend E tc] extends the derivability structure [E] to an extended signature, where [tc] is the
typing/congruence rules of a new symbol. We also use a custom data type in order to add the two new
rules, in order to get something readable.
-}
data Ext (A : JudgmentArity → Set) (ar : SyntaxArity) : JudgmentArity → Set where
  typingrule : Ext A ar (TArity ar)
  congruencerule : Ext A ar (CArity ar)
  prev : {ar' : JudgmentArity} → A ar' → Ext A ar ar'

extend : {Σ : Signature} (E : DerivabilityStructure Σ)
         {ar : SyntaxArity}
         (tc : DerivationRules Σ ar 0)
         → DerivabilityStructure (ExtSig Σ ar)
Rules (extend E {ar} tc) = Ext (Rules E) ar
derivationRule (extend E tc) (prev r) = ↑DerivationRule (derivationRule E r)
derivationRule (extend E tc) typingrule = typingdrule tc
derivationRule (extend E tc) congruencerule = congruencedrule tc


{- Typing rules for basic metavariables (simply a derivable type in the empty context) -}

record BMTypingRule {Σ : Signature} (E : DerivabilityStructure Σ) : Set where
  constructor bmtypingrule
  field
    type : TyExpr Σ 0
    der : Derivable E {Γ = ◇} (◇ ⊢ type)
open BMTypingRule public

{- Arities of basic metavariables -}

BMArity : SyntaxArity
args BMArity = []
sort BMArity = Tm

{- The derivation rules corresponding to a basic metavariable (on the extended signature). -}

BMRules : {Σ : Signature} {E : DerivabilityStructure Σ} {n : ℕ}
          (t : BMTypingRule E)
          → DerivationRules Σ BMArity n
rule (typingdrule (BMRules t)) ↑ Γ [] = return (◇ ⊢ (↑ $ new) [] :> ↑Expr (⊂Ext ↑) (weaken^ (type t)))
rule (congruencedrule (BMRules t)) ↑ Γ [] = return (◇ ⊢ (↑ $ new) [] == (↑ $ new) [] :> ↑Expr (⊂Ext ↑) (weaken^ (type t)))


{- Arities of metavariables -}

MArityArgs : ℕ → SyntaxArityArgs
MArityArgs zero = []
MArityArgs (suc n) = MArityArgs n , (0 , Tm)

MArity : ℕ → SyntaxSort → SyntaxArity
args (MArity n k) = MArityArgs n
sort (MArity n k) = k

{- [ExtSig^ Σ args] extends the signature [Σ] by symbols for metavariables with arities given by [args] -}

ExtSig^ : Signature → SyntaxArityArgs → Signature
ExtSig^ Σ [] = Σ
ExtSig^ Σ (args , (n , k)) = ExtSig (ExtSig^ Σ args) (MArity n k)

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

extend^BM : {Σ : Signature} (E : DerivabilityStructure Σ) {n : ℕ} (ts : MTypingRulePremises E n) → DerivabilityStructure (ExtSig^ Σ (MArityArgs n))

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
Given two signatures [Σ] and [Σ'], we can map from a signature extended over [Σ] to [Σ'] as long as
we can map from [Σ] to [Σ'] and that we have terms [as] in [Σ'] to replace the new symbols.
[SubstBM E ↑ as] represents that map.
-}

SubstBM : {Σ Σ' : Signature} {m n : ℕ}
      → Sub Σ Σ' m
      → Args Σ' m (MArityArgs n)
      → Sub (ExtSig^ Σ (MArityArgs n)) Σ' m
SubstBM {n = zero} ↑ [] = ↑
SubstBM {n = suc n} ↑ (as , a) $ prev s = SubstBM ↑ as $ s
(SubstBM {n = suc n} ↑ (as , a) $ new) [] = weaken^ a

{-
The derivation rules associated to a typing rule for a metavariable.
-}

MTypingRule-TArgs : {Σ Σ' : Signature} (E : DerivabilityStructure Σ) {n m : ℕ} (↑ : Sub Σ Σ' m) {Γ : Ctx Σ' m}
                   (ts : MTypingRulePremises E n) (js : DerivationRulePremises Σ' Γ (TArityArgs (MArityArgs n)))
                   → Partial (Args Σ' m (MArityArgs n))
MTypingRule-TArgs E ↑ [] [] = return []
MTypingRule-TArgs E ↑ (ts , t) (js , ◇ ⊢ a :> A) = do
  as ← MTypingRule-TArgs E ↑ ts js
  assume (A ≡ ↑Expr (SubstBM ↑ as) (weaken^ (type t)))
  return (as , a)

MTypingRule-TRule : {Σ : Signature} (E : DerivabilityStructure Σ) {n : ℕ} {k : SyntaxSort}
                    (t : MTypingRule E n k) {m : ℕ}
                    → DerivationRule (ExtSig Σ (MArity n k)) (TArity (MArity n k)) m
rule (MTypingRule-TRule E (Ty ts)) ↑ Γ js = do
  as ← MTypingRule-TArgs E (⊂Ext ↑) ts js
  return (◇ ⊢ (↑ $ new) as)
rule (MTypingRule-TRule E (Tm ts t)) ↑ Γ js = do
  as ← MTypingRule-TArgs E (⊂Ext ↑) ts js
  return (◇ ⊢ (↑ $ new) as :> ↑Expr (SubstBM (⊂Ext ↑) as) (weaken^ (type t)))

MTypingRule-CArgs : {Σ Σ' : Signature} (E : DerivabilityStructure Σ) {n m : ℕ} (↑ : Sub Σ Σ' m) {Γ : Ctx Σ' m}
                   (ts : MTypingRulePremises E n) (js : DerivationRulePremises Σ' Γ (CArityArgs (MArityArgs n)))
                   → Partial (Args Σ' m (MArityArgs n) × Args Σ' m (MArityArgs n))
MTypingRule-CArgs E ↑ [] [] = return ([] , [])
MTypingRule-CArgs E ↑ (ts , t) (js , ◇ ⊢ a == a' :> A) = do
  (as , as') ← MTypingRule-CArgs E ↑ ts js
  assume (A ≡ ↑Expr (SubstBM ↑ as) (weaken^ (type t)))
  assume (A ≡ ↑Expr (SubstBM ↑ as') (weaken^ (type t)))
  return ((as , a) , (as' , a'))

MTypingRule-CRule : {Σ : Signature} (E : DerivabilityStructure Σ) {n : ℕ} {k : SyntaxSort}
                    (t : MTypingRule E n k) {m : ℕ}
                    → DerivationRule (ExtSig Σ (MArity n k)) (CArity (MArity n k)) m
rule (MTypingRule-CRule E (Ty ts)) ↑ Γ js = do
  (as , as') ← MTypingRule-CArgs E (⊂Ext ↑) ts js
  return (◇ ⊢ (↑ $ new) as == (↑ $ new) as')
rule (MTypingRule-CRule E (Tm ts t)) ↑ Γ js = do
  (as , as') ← MTypingRule-CArgs E (⊂Ext ↑) ts js
  return (◇ ⊢ (↑ $ new) as == (↑ $ new) as' :> ↑Expr (SubstBM (⊂Ext ↑) as) (weaken^ (type t)))


MRules : {Σ : Signature} {E : DerivabilityStructure Σ} {n : ℕ} {k : SyntaxSort}
                    (t : MTypingRule E n k) {m : ℕ}
                    → DerivationRules Σ (MArity n k) m
typingdrule (MRules t) = MTypingRule-TRule _ t
congruencedrule (MRules t) = MTypingRule-CRule _ t


{- TODO -}

postulate
  Subst1 : {Σ : Signature} {n m : ℕ} {{p : m ≤ n}} {k : SyntaxSort} → Expr Σ (suc n) k → TmExpr Σ m → Expr Σ n k
-- Subst1 (var last) a = weaken^ a
-- Subst1 (var (prev x)) a = var x
-- Subst1 (sym s x) a = {!!}

Subst : {Σ : Signature} {m n : ℕ} {k : SyntaxSort} → Expr Σ (m + n) k → Args Σ n (MArityArgs m) → Expr Σ n k
Subst {m = zero} e [] = e
Subst {m = suc m} e (as , a) = Subst (Subst1 e a) as

SubstM : {Σ Σ' : Signature} {m : ℕ} {args : SyntaxArityArgs}
      → Sub Σ Σ' m
      → Args Σ' m args
      → Sub (ExtSig^ Σ args) Σ' m
SubstM ↑ [] = ↑
SubstM ↑ (as , a) $ prev s = SubstM ↑ as $ s
(SubstM ↑ (as , a) $ new) bs = Subst (weaken^' a) bs

{- TODO -}

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

{- TODO -}

data TypingRule {Σ : Signature} (E : DerivabilityStructure Σ) (args : SyntaxArityArgs) : (k : SyntaxSort) → Set where
  Ty : TypingRulePremises E args → TypingRule E args Ty
  Tm : (ts : TypingRulePremises E args) → BMTypingRule (extend^M E ts) → TypingRule E args Tm


{- The derivation rules associated to a typing rule. -}

Vars : {Σ : Signature} {n : ℕ} (m : ℕ) → Args Σ (n + m) (MArityArgs n)
Vars {n = zero} m = []
Vars {n = suc n} m = weaken^A (Vars m) , var last

check-DepCtx : {Σ Σ' : Signature} {m n : ℕ} {args : SyntaxArityArgs}
               {E : DerivabilityStructure (ExtSig^ Σ args)}
               → Sub Σ Σ' m → Args Σ' m args
               → MTypingRulePremises E n → DepCtx Σ' m n → Partial Unit
check-DepCtx ↑ as [] ◇ = return tt
check-DepCtx {m = m} ↑ as (t's , t) (Δ , A) = do
  check-DepCtx ↑ as t's Δ
  assume (A ≡ ↑Expr (SubstM (liftSub ↑) (weaken^A as)) (↑Expr (SubstBM id⊂ (Vars m)) (weaken^ (type t))))
  return tt

TypingRule-TArgs : {Σ Σ' : Signature} (E : DerivabilityStructure Σ) {args : SyntaxArityArgs} {m : ℕ} (↑ : Sub Σ Σ' m) {Γ : Ctx Σ' m}
                   (ts : TypingRulePremises E args) (js : DerivationRulePremises Σ' Γ (TArityArgs args))
                   → Partial (Args Σ' m args)
TypingRule-TArgs E ↑ [] [] = return []
TypingRule-TArgs E {args = args , (n , Ty)} {m} ↑ (ts , Ty t's) (js , Δ ⊢ A) = do
  as ← TypingRule-TArgs E ↑ ts js
  check-DepCtx ↑ as t's Δ
  return (as , A)
TypingRule-TArgs E {args = args , (n , Tm)} {m} ↑ (ts , Tm t's t) (js , Δ ⊢ u :> A) = do
  as ← TypingRule-TArgs E ↑ ts js
  check-DepCtx ↑ as t's Δ
  assume (A ≡ ↑Expr (SubstM (liftSub ↑) (weaken^A as)) (↑Expr (SubstBM id⊂ (Vars m)) (weaken^ (type t))))
  return (as , u)

TypingRule-TRule : {Σ : Signature} (E : DerivabilityStructure Σ) {args : SyntaxArityArgs} {k : SyntaxSort}
                   (t : TypingRule E args k) {m : ℕ}
                   → DerivationRule (ExtSig Σ (mkarity args k)) (TArity (mkarity args k)) m
rule (TypingRule-TRule E (Ty ts)) ↑ Γ js = do
  as ← TypingRule-TArgs E (⊂Ext ↑) ts js
  return (◇ ⊢ (↑ $ new) as)
rule (TypingRule-TRule E (Tm ts t) {m = m}) ↑ Γ js = do
  as ← TypingRule-TArgs E (⊂Ext ↑) ts js
  return (◇ ⊢ (↑ $ new) as :> ↑Expr (SubstM (⊂Ext (liftSub ↑)) (weaken^A as)) (↑Expr (SubstBM id⊂ (Vars m)) (weaken^ (type t))))

TRules : {Σ : Signature} {E : DerivabilityStructure Σ} {ar : SyntaxArity}
        (t : TypingRule E (args ar) (sort ar)) {m : ℕ}
        → DerivationRules Σ ar m
typingdrule (TRules t) = TypingRule-TRule _ t
congruencedrule (TRules t) = {!TODO!}


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
  newsym : (t : TypeTheory) {ar : SyntaxArity} (r : TypingRule (TTDer t) (args ar) (sort ar)) → TypeTheory
--  neweq : (t : TypeTheory) → {!!} → TypeTheory

TTSig ◇ = Σ₀
TTSig (newsym t {ar} r) = ExtSig (TTSig t) ar
--TTSig (neweq t _) = TTSig t

TTDer ◇ = E₀
TTDer (newsym t r) = extend (TTDer t) (TRules r)
--TTDer (neweq t r) = {!!}


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


{- Examples -}

{- A type, x : A ⊢ B type, and Π-introduction -}

module _ where
  TypingRuleA : MTypingRule E₀ 0 Ty
  TypingRuleA = Ty []

  TypingRuleB : MTypingRule (extend E₀ (MRules TypingRuleA)) 1 Ty
  TypingRuleB = Ty ([] , bmtypingrule (sym 0 []) (apply 0 []))

  TypingRuleΠ : TypingRule E₀ ([] , (0 , Ty) , (1 , Ty)) Ty
  TypingRuleΠ = Ty ([] , TypingRuleA , TypingRuleB)

  TypingRuleλ : TypingRule (extend E₀ (TRules TypingRuleΠ)) ([] , (0 , Ty) , (1 , Ty) , (1 , Tm)) Tm
  TypingRuleλ = Tm ([] , Ty []
                       , Ty ([] , bmtypingrule (sym 0 []) (apply 0 []))
                       , Tm ([] , bmtypingrule (sym 1 []) (apply 1 []))
                            (bmtypingrule (sym 1 ([] , sym 0 []))
                                          (apply 1 ([] , (apply 0 [])))))
                   (bmtypingrule (sym 3 ([] , sym 2 [] , sym 1 ([] , var last)))
                                 (apply 3 ([] , apply 2 [] , flat {j = (◇ , _) ⊢ _} (apply 1 ([] , apply (prev (prev (prev (prev (var 0))))) ([] , apply 2 []))))))

  TypingRuleapp : TypingRule (extend (extend E₀ (TRules TypingRuleΠ)) (TRules TypingRuleλ)) ([] , (0 , Ty) , (1 , Ty) , (0 , Tm) , (0 , Tm)) Tm
  TypingRuleapp = Tm ([] , Ty []
                         , Ty ([] , (bmtypingrule (sym 0 []) (apply 0 [])))
                         , Tm [] (bmtypingrule (sym 3 ([] , sym 1 [] , sym 0 ([] , var last)))
                                               (apply 3 ([] , apply 1 [] , flat {j = (◇ , _) ⊢ _} (apply 0 ([] , apply (prev (prev (prev (prev (var 0))))) ([] , apply 1 []))))))
                         , Tm [] (bmtypingrule (sym 2 []) (apply 2 [])))
                     (bmtypingrule (sym 2 ([] , sym 0 [])) (apply 2 ([] , apply 0 [])))

  Π-TT : TypeTheory
  Π-TT = newsym (newsym (newsym ◇ TypingRuleΠ) TypingRuleλ) TypingRuleapp


{- Formation rule, introduction rule, and elimination rule for the natural numbers -}

module _ where
  TypingRuleℕ : MTypingRule E₀ 0 Ty
  TypingRuleℕ = Ty []

  E₁ : DerivabilityStructure _
  E₁ = extend E₀ (MRules TypingRuleℕ)

  TypingRule0 : MTypingRule E₁ 0 Tm
  TypingRule0 = Tm [] (bmtypingrule (sym 0 []) (apply 0 []))

  E₂ : DerivabilityStructure _
  E₂ = extend E₁ (MRules TypingRule0)

  TypingRuleS : MTypingRule E₂ 1 Tm
  TypingRuleS = Tm ([] , bmtypingrule (sym 1 []) (apply 1 []))
                        (bmtypingrule (sym 2 []) (apply 2 []))

  E₃ : DerivabilityStructure _
  E₃ = extend E₂ (MRules TypingRuleS)

  TypingRuleP : MTypingRule E₃ 1 Ty
  TypingRuleP = Ty ([] , bmtypingrule (sym 2 []) (apply 2 []))

  E₄ : DerivabilityStructure _
  E₄ = extend E₃ (MRules TypingRuleP)

  TypingRuled0 : MTypingRule E₄ 0 Tm
  TypingRuled0 = Tm [] (bmtypingrule (sym 3 []) (apply 3 []))

  E₅ : DerivabilityStructure _
  E₅ = extend E₄ (MRules TypingRuled0)

  TypingRuledS : MTypingRule E₅ 2 Tm
  TypingRuledS = Tm ([] , bmtypingrule (sym 4 []) (apply 4 [])
                        , bmtypingrule (sym 2 ([] , sym 0 [])) (apply 2 ([] , apply 0 [])))
                    (bmtypingrule (sym 3 ([] , (sym 4 ([] , (sym 1 [])))))
                                  (apply 3 ([] , apply 4 ([] , apply 1 []))))

  E₆ : DerivabilityStructure _
  E₆ = extend E₅ (MRules TypingRuledS)

  TypingRulen : MTypingRule E₆ 0 Tm
  TypingRulen = Tm [] (bmtypingrule (sym 5 []) (apply 5 []))

  TypingRuleℕ-elim : TypingRule E₃ ([] , (1 , Ty) , (0 , Tm) , (2 , Tm) , (0 , Tm)) Tm
  TypingRuleℕ-elim = Tm ([] , TypingRuleP , TypingRuled0 , TypingRuledS , TypingRulen)
                        (bmtypingrule (sym 3 ([] , (sym 0 []))) (apply 3 ([] , apply 0 [])))
