{-# OPTIONS --rewriting --prop --exact-split #-}

open import common

{-
An arity is something of the form (((n_1, k_1), …, (n_l, k_l)) , k), where the n_i are natural
numbers and the k_i and k are sorts. We will use two different types of sorts, so we parametrize
arities by the type of sorts.
The type [ArityArgs Sort] represents the first components of arities (the list), and [Arity Sort]
represents arities.
-}

data ArityArgs (Sort : Set) : Set where
  [] : ArityArgs Sort
  _,_ : ArityArgs Sort → (ℕ × Sort) → ArityArgs Sort

record Arity (Sort : Set) : Set where
  constructor _,_
  field
    args : ArityArgs Sort
    sort : Sort
open Arity public


SyntaxArityArgs = ArityArgs SyntaxSort
SyntaxArity = Arity SyntaxSort

{-
A signature consists of symbols, which are indexed by their arities. To have instead a set of
symbols and an arity function is very inconvenient.
-}

record Signature : Set₁ where
  field
    Symbols : SyntaxArity → Set
open Signature public

{-
Expressions are indexed by their syntactic class and their scope. An expression is either a variable
or a symbol applied to the appropriate number of arguments.
The type [Expr Σ n] is defined simultaneously with the type [Args Σ n args] which represents the
type of the arguments of a symbol with arity (args, _). 
-}

data Args (Σ : Signature) (n : ℕ) : SyntaxArityArgs → Set

data Expr (Σ : Signature) (n : ℕ) : SyntaxSort → Set where
  var : VarPos n → Expr Σ n Tm
  sym : {ar : SyntaxArity} (s : Symbols Σ ar) → Args Σ n (args ar) → Expr Σ n (sort ar)

data Args Σ n where
  [] : Args Σ n []
  _,_ : {m : ℕ} {k : SyntaxSort} {args : SyntaxArityArgs}
      → Args Σ n args
      → Expr Σ (n + m) k
      → Args Σ n (args , (m , k))

{- Abbreviations for type-/term-expressions -}

TyExpr : (Σ : Signature) → ℕ → Set
TyExpr Σ n = Expr Σ n Ty

TmExpr : (Σ : Signature) → ℕ → Set
TmExpr Σ n = Expr Σ n Tm

{-
weakenV : {n m : ℕ} {{_ : n ≤ m}} (p : WeakPos n) → VarPos n → VarPos m
weakenV ⦃ ≤r ⦄ p x = x
weakenV ⦃ ≤S r ⦄ last x = prev (weakenV {{r}} last x)
weakenV ⦃ ≤S r ⦄ (prev p) last = last
weakenV ⦃ ≤S r ⦄ (prev p) (prev x) = prev (weakenV {{≤P (≤S r)}} p x)
-}

-- weakenVL : {n m : ℕ} {{_ : n ≤ m}} → VarPos n → VarPos m
-- weakenVL {{ ≤r }} x = x
-- weakenVL {{ ≤S p }} x = prev (weakenVL {{p}} x)

-- postulate
--   weakenV : {n m : ℕ} {{_ : n ≤ m}} (p : WeakPos n) → VarPos n → VarPos m
-- weakenV {m = _} ⦃ ≤r ⦄ last last = last
-- weakenV {m = _} ⦃ ≤S r ⦄ last last = prev (weakenV {{r}} last last)
-- weakenV {m = suc m} ⦃ r ⦄ (prev p) last = last
-- weakenV {m = suc m} ⦃ ≤r ⦄ last (prev x) = prev x
-- weakenV {m = suc m} ⦃ ≤S r ⦄ last (prev x) = prev (weakenV {m = m} {{≤P (≤S r)}} last x)
-- weakenV {m = suc m} ⦃ r ⦄ (prev p) (prev x) = prev (weakenV {m = m} {{≤P r}} p x)

-- weakenV {m = suc m}       (prev wp) last = last
-- weakenV {m = suc m} {{p}} (prev wp) (prev x) = prev (weakenV {{≤P p}} wp x)
-- weakenV {m = suc m} ⦃ ≤r ⦄ last x = x
-- weakenV {m = suc m} ⦃ ≤S r ⦄ last x = prev (weakenV {{r}} last x)

-- weakenV {m = suc m} ⦃ p ⦄ (prev wp) last = last
-- weakenV {m = suc m} ⦃ p ⦄ (prev wp) (prev x) = prev (weakenV {{≤P p}} wp x)
-- weakenV {m = suc m} ⦃ ≤r ⦄ last x = x
-- weakenV {m = suc m} ⦃ ≤S p ⦄ last x = prev (weakenV {{p}} last x)

postulate
  TODO : {A : Set} → A
  
weaken : {Σ : Signature} {k : _} {n m : ℕ} {{_ : n ≤ m}} (p : WeakPos n) → Expr Σ n k → Expr Σ m k
weakenA : {Σ : Signature} {ar : _} {n m : ℕ} {{_ : n ≤ m}} (p : WeakPos n) → Args Σ n ar → Args Σ m ar

weaken p (var x) = var (weakenV p x)
weaken p (sym s es) = sym s (weakenA p es)

weakenA p [] = []
weakenA {{q}} p (_,_ {m = m} es e) = (weakenA p es , weaken {{≤+ m {{q}}}} (weakenPos (≤-+ {m = m}) p) e)


weaken' : {Σ : Signature} {k : _} {n m : ℕ} {{_ : n ≤ m}} (p : WeakPos n) → Expr Σ n k → Expr Σ m k
weaken' ⦃ ≤r ⦄ p e = e
weaken' ⦃ ≤S q ⦄ p e = weaken {{≤S q}} p e


weakenL : {Σ : Signature} {k : _} {m n : ℕ} → Expr Σ m k → Expr Σ (m + n) k
weakenL {n = zero} e = e
weakenL {n = suc n} e = weaken last e

weaken0 : {Σ : Signature} {k : _} {n : ℕ} → Expr Σ 0 k → Expr Σ n k
weaken0 e = weaken {{0≤}} last e

weaken0' : {Σ : Signature} {k : _} {n : ℕ} → Expr Σ 0 k → Expr Σ n k
weaken0' {n = zero} e = e
weaken0' {n = suc n} e = weaken last e

weakenAL : {Σ : Signature} {ar : _} {m n : ℕ} → Args Σ m ar → Args Σ (m + n) ar
weakenAL {n = zero} es = es
weakenAL {n = suc n} es = weakenA last es

prev^last : (n l : ℕ) → WeakPos (n + l)
prev^last n zero = last
prev^last n (suc l) = prev (prev^last n l)

-- weaken≤ : {Σ : Signature} {k : _} {n m l : ℕ} {{_ : n ≤ m}} → Expr Σ (n + l) k → Expr Σ (m + l) k
-- weaken≤ ⦃ ≤r ⦄ e = e
-- weaken≤ {n = n} {l = l} ⦃ ≤S p ⦄ e = weaken {{TODO}} (prev^last n l) e

-- weaken^V' : {l m n : ℕ} → VarPos (l + m) → VarPos (l + n + m)
-- weaken^' : {Σ : Signature} {k : _} {l m n : ℕ} → Expr Σ (l + m) k → Expr Σ (l + n + m) k
-- weaken^A' : {Σ : Signature} {ar : _} {l m n : ℕ} → Args Σ (l + m) ar → Args Σ (l + n + m) ar

-- weaken^V' {zero} {m} {zero} k = k
-- weaken^V' {zero} {m} {suc n} k = prev (weaken^V' {zero} {m} {n} k)
-- weaken^V' {suc l} {m} {n} last = last
-- weaken^V' {suc l} {m} {n} (prev k) = prev (weaken^V' {l} {m} {n} k)

-- weaken^' {l = l} {m} {n} (var k) = var (weaken^V' {l = _} {m} {n} k)
-- weaken^' {l = l} {m} {n} (sym s x) = sym s (weaken^A' {l = _} {m} {n} x)

-- weaken^A' [] = []
-- weaken^A' {l = l} {m} {n} (_,_ {m = _} a x) = (weaken^A' {l = _} {m} {n} a , weaken^' {l = _} {m} {n} x)

-- -- this should not be defined as iterated weakening, it should reduce on expressions
-- weaken^ : {Σ : Signature} {k : _} {l n m : ℕ} {{p : n ≤ m}} → Expr Σ (l + n) k → Expr Σ (l + m) k
-- weaken^ {l = l} {n} {m} {{p}} k = weaken^' {l = l} {{!n!}} {{!!}} k

-- weaken^A : {Σ : Signature} {ar : _} {l n m : ℕ} {{p : n ≤ m}} → Args Σ (l + n) ar → Args Σ (l + m) ar
-- weaken^A {{p}} = weaken^A' {{p}}


-- weakenV≤r : {n : ℕ} {p : WeakPos n} (v : VarPos n) → weakenV {{≤r}} p v ≡ v
-- weakenV≤r {p = last} last = refl
-- weakenV≤r {p = prev p} last = refl
-- weakenV≤r {p = last} (prev v) = refl
-- weakenV≤r {p = prev p} (prev v) = ap prev (weakenV≤r {p = p} v)

-- weaken≤r : {Σ : Signature} {k : _} {n : ℕ} {p : WeakPos n} (e : Expr Σ n k) → weaken p e ≡ e
-- weakenA≤r : {Σ : Signature} {k : _} {n : ℕ} {p : WeakPos n} (as : Args Σ n k) → weakenA p as ≡ as

-- weaken≤r {p = p} (var x) = ap var (weakenV≤r {p = p} x)
-- weaken≤r (sym s x) = ap (sym s) (weakenA≤r x)

-- weakenA≤r [] = refl
-- weakenA≤r (es , e) = ap2 _,_ (weakenA≤r es) (weaken≤r e)

-- -- {-# REWRITE weaken^'≤r #-}


{- Contexts, [Ctx Σ n] represents contexts in signature [Σ] and of length [n] -}

data Ctx (Σ : Signature) : ℕ → Set where
  ◇ : Ctx Σ 0
  _,_ : {n : ℕ} (Γ : Ctx Σ n) (A : TyExpr Σ n) → Ctx Σ (suc n)


{- TODO
Dependent contexts, [DepCtx Σ n m] represents contexts in signature [Σ], in scope [n], and of
length [m]. They are built in the other direction compared to [Ctx], we add types to the left
instead of adding them to the right. The reason is that the "purpose" of dependent contexts is to
move the types one by one to the context on the left.
-}

data DepCtx (Σ : Signature) (n : ℕ) : ℕ → Set where
  ◇ : DepCtx Σ n 0
  _,_ : {m : ℕ} → DepCtx Σ n m → TyExpr Σ (n + m) → DepCtx Σ n (suc m)

{-
Extraction of types from contexts.
We need this partial version instead of the total well-typed one (below, not used).
-}

get : {Σ : Signature} {n : ℕ} (k : ℕ) → Ctx Σ n → Partial (VarPos n × TyExpr Σ n)
get k ◇ = fail
get zero (Γ , A) = return (last , weaken last A)
get (suc k) (Γ , X) = do
  (k' , A) ← get k Γ
  return (prev k' , weaken last A)

getTotal : {Σ : Signature} {n : ℕ} (k : VarPos n) → Ctx Σ n → TyExpr Σ n
getTotal last (Γ , A) = weaken last A
getTotal (prev k) (Γ , X) = weaken last (getTotal k Γ)


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
expressions to expressions (as they may bind new variables).

Therefore we define [(Σ →Sig Σ') n] which represents maps from symbols of [Σ] to expression-building
functions for signature [Σ'], and which works for any scope above (and including) [n].
-}

record _→Sig_ (Σ Σ' : Signature) (n : ℕ) : Set where
  constructor sub
  field
    _$_ : {m : ℕ} {{p : n ≤ m}} {ar : SyntaxArity} (s : Symbols Σ ar) → Args Σ' m (args ar) → Expr Σ' m (sort ar)
open _→Sig_ public

{- Identity map -}

idSig : {n : ℕ} {Σ : Signature} → (Σ →Sig Σ) n
idSig $ s = sym s

{- Lifting at a higher scope -}

liftSig : {m n : ℕ} {Σ Σ' : Signature} → (Σ →Sig Σ') m → (Σ →Sig Σ') (m + n)
(liftSig {n = n} ↑ $ s) x = _$_ ↑ {{≤tr {{≤-+ {m = n}}}}} s x

{- Lifting of a map between signatures to expressions -}

↑Expr : {Σ Σ' : Signature} {n : ℕ} {k : SyntaxSort} → (Σ →Sig Σ') n → Expr Σ n k → Expr Σ' n k
↑Args : {Σ Σ' : Signature} {n : ℕ} {args : SyntaxArityArgs} → (Σ →Sig Σ') n → Args Σ n args → Args Σ' n args

↑Expr ↑ (var x) = var x
↑Expr ↑ (sym s x) = (↑ $ s) (↑Args ↑ x)

↑Args ↑ [] = []
↑Args ↑ (_,_ {m = m} es e) = ↑Args ↑ es , ↑Expr (liftSig ↑) e


{-
[ExtSig Σ ar] extends the signature [Σ] by an arity [ar].
In order to add a symbol only at the correct arity, we use an inductive family (another possibility
would be to use decidable equality of arities but that would be very ugly).
-}

data ExtSigSymbols (S : SyntaxArity → Set) (ar : SyntaxArity) : SyntaxArity → Set where
  prev : {ar' : SyntaxArity} → S ar' → (ExtSigSymbols S ar) ar'
  new : (ExtSigSymbols S ar) ar

ExtSig : Signature → SyntaxArity → Signature
Symbols (ExtSig Σ ar) = ExtSigSymbols (Symbols Σ) ar

{- If an extended signature maps to [Σ'], then the original signature too. -}
Ext→ : {Σ Σ' : Signature} {ar : SyntaxArity} {n : ℕ} → (ExtSig Σ ar →Sig Σ') n → (Σ →Sig Σ') n
Ext→ ↑ $ s = ↑ $ (prev s)

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

{- Example
ExtSig^ Σ ((0, Ty), (1, Ty)) = extend Σ with one symbol of arity (() , Ty) and
                                             one symbol of arity ((0 , Tm), Ty)
-}


{-
Given two signatures [Σ] and [Σ'], we can map from a signature extended over [Σ] to [Σ'] as long as
we can map from [Σ] to [Σ'] and that we have terms [as] in [Σ'] to replace the new symbols.
[SubstM ↑ as] represents that map.
-}

-- trExpr : {Σ : Signature} {n n' : ℕ} (p : n === n') {k : SyntaxSort} → Expr Σ n k → Expr Σ n' k
-- trExpr refl u = u

-- trExpr! : {Σ : Signature} {n n' : ℕ} (p : n === n') {k : SyntaxSort} → Expr Σ n' k → Expr Σ n k
-- trExpr! refl u = u

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

trV  : {n m : ℕ} → n ≡ m → VarPos n → VarPos m
trV {m = suc m} p last = last
trV {m = suc m} p (prev x) = prev (trV (ap pred p) x)

tr  : {Σ : Signature} {k : SyntaxSort} {n m : ℕ} → n ≡ m → Expr Σ n k → Expr Σ m k
trA : {Σ : Signature} {ar : SyntaxArityArgs} {n m : ℕ} → n ≡ m → Args Σ n ar → Args Σ m ar

tr p (var x) = var (trV p x)
tr p (sym s es) = sym s (trA p es)

trA p [] = []
trA p (es , x) = (trA p es , tr (ap (_+ _) p) x)

tr! : {Σ : Signature} {k : SyntaxSort} {n m : ℕ} → m ≡ n → Expr Σ n k → Expr Σ m k
tr! p e = tr (! p) e


data Mor (Σ : Signature) (n : ℕ) : ℕ → Set where 
 ◇ : Mor Σ n 0
 _,_ : {m : ℕ} (δ : Mor Σ n m) (u : TmExpr Σ n) → Mor Σ n (suc m)

weakenMor : {Σ : Signature} {n m : ℕ} → Mor Σ m n → Mor Σ (suc m) n
weakenMor ◇ = ◇
weakenMor (δ , u) = (weakenMor δ , weaken last u)

idMor : {Σ : Signature} {n : ℕ} → Mor Σ n n
idMor {n = zero} = ◇
idMor {n = suc n} = (weakenMor idMor , var last)

weakenMor+ : {Σ : Signature} (k : ℕ) {n m : ℕ} → Mor Σ m n → Mor Σ (m + k) (n + k)
weakenMor+ zero δ = δ
weakenMor+ (suc k) δ = (weakenMor (weakenMor+ k δ) , var last)

SubstMor  : {Σ : Signature} {n m : ℕ} {k : SyntaxSort} → Expr Σ n k → Mor Σ m n → Expr Σ m k
SubstAMor : {Σ : Signature} {n m : ℕ} {args : SyntaxArityArgs} → Args Σ n args → Mor Σ m n → Args Σ m args

SubstMor (var last) (δ , u) = u
SubstMor (var (prev x)) (δ , u) = SubstMor (var x) δ
SubstMor (sym s es) δ = sym s (SubstAMor es δ)

SubstAMor [] δ = []
SubstAMor (_,_ {m = m} es x) δ = (SubstAMor es δ , SubstMor x (weakenMor+ m δ))


-- Subst1  : {Σ : Signature} {n : ℕ} (m : ℕ) {k : SyntaxSort} → Expr Σ (suc n + m) k → TmExpr Σ n → Expr Σ (n + m) k
-- Subst1A : {Σ : Signature} {n : ℕ} (m : ℕ) {args : SyntaxArityArgs} → Args Σ (suc n + m) args → TmExpr Σ n → Args Σ (n + m) args

-- Subst1 n (sym s x) a = sym s (Subst1A n x a)
-- Subst1 zero (var last) a = a
-- Subst1 zero (var (prev x)) a = var x
-- Subst1 (suc m) (var last) a = var last
-- Subst1 (suc m) (var (prev x)) a = weaken last (Subst1 m (var x) a)

-- Subst1A m [] a = []
-- Subst1A {n = n} m (_,_ {m = k} es e) a = (Subst1A m es a , tr! (assoc {n} {m} {k}) (Subst1 (m + k) (tr (assoc {suc n} {m} {k}) e) a))


Subst  : {Σ : Signature} {l m : ℕ} {k : SyntaxSort} → Expr Σ (m + l) k → Args Σ m (MArityArgs l) → Expr Σ m k
Subst {l = zero} e [] = e
Subst {l = suc l} {m} e (as , a) = Subst (SubstMor e (idMor , weakenL a)) as

SubstM : {Σ Σ' : Signature} {m : ℕ} {args : SyntaxArityArgs}
      → (Σ →Sig Σ') m
      → Args Σ' m args
      → ((ExtSig^ Σ args) →Sig Σ') m
SubstM ↑ [] = ↑
SubstM ↑ (as , a) $ prev s = SubstM ↑ as $ s
(SubstM ↑ (_,_ {m = l} as a)) $ new = Subst (weaken' {{≤+ l}} (prev^last _ l) a)

subst : {n m : ℕ} {k : SyntaxSort} {Σ Σ' : Signature} (↑ : (Σ →Sig Σ') n) {args : SyntaxArityArgs} (as : Args Σ' (n + m) args)
      → Expr (ExtSig^ Σ args) (n + m) k
      → Expr Σ' (n + m) k
subst {m = m} ↑ as e = ↑Expr (SubstM (liftSig ↑) as) e

-- {-
-- Example:

-- args = ((0, Ty), (1, Ty), (1, Tm))
-- ExtSig^ Σ args = Σ + {A} + {B} + {u} where A has arity ((), Ty), B has arity ((0, Tm), Ty), u has arity ((0, Tm), Tm)
-- To get a map from it to Σ', we need
-- - a map from Σ to Σ'
-- - a type expression in Σ' (for A)
-- - a type expression in Σ' in scope (m + 1)  (for B)
-- - a term expression in Σ' in scope (m + 1)  (for u)
-- -}
