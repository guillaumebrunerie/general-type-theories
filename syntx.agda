{-# OPTIONS --rewriting --prop #-}

open import common

{-
An *arity* is something of the form (((n_1, k_1), …, (n_l, k_l)) , k), where the n_i are natural
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
      → Expr Σ (m + n) k
      → Args Σ n (args , (m , k))

{- Abbreviations for type-/term-expressions -}

TyExpr : (Σ : Signature) → ℕ → Set
TyExpr Σ n = Expr Σ n Ty

TmExpr : (Σ : Signature) → ℕ → Set
TmExpr Σ n = Expr Σ n Tm

{- Weakening at a certain position -}

weakenV : {n : ℕ} → VarPos n → WeakPos n → VarPos (suc n)
weakenV x last = prev x
weakenV last (prev k) = last
weakenV (prev x) (prev k) = prev (weakenV x k)

weaken : {Σ : Signature} {n : ℕ} {k : SyntaxSort} → Expr Σ n k → WeakPos n → Expr Σ (suc n) k
weakenA : {Σ : Signature} {n : ℕ} {ar : SyntaxArityArgs} → Args Σ n ar
            → WeakPos n → Args Σ (suc n) ar

weaken (var x) k = var (weakenV x k)
weaken (sym s args) k = sym s (weakenA args k)

weakenA [] k = []
weakenA (args , e) k = weakenA args k , weaken e (weakenWeakPos _ k)

weakenL : {Σ : Signature} {n : ℕ} {k : SyntaxSort} → Expr Σ n k → Expr Σ (suc n) k
weakenL e = weaken e last

{- Weakening at a group of positions -}

postulate  -- TODO
  weaken^V : {n m l : ℕ} {{p : n ≤ m}} → VarPos (l + n) → VarPos (l + m)

weaken^' : {Σ : Signature} {k : _} {n m l : ℕ} {{p : n ≤ m}} → Expr Σ (l + n) k → Expr Σ (l + m) k
weaken^A' : {Σ : Signature} {ar : _} {n m l : ℕ} {{p : n ≤ m}} → Args Σ (l + n) ar → Args Σ (l + m) ar

weaken^' (var k) = var (weaken^V k)
weaken^' (sym s x) = sym s (weaken^A' x)

weaken^A' [] = []
weaken^A' {m = m} (a , x) = (weaken^A' a , weaken^' {m = m} x)

weaken^ : {Σ : Signature} {k : _} {n m : ℕ} {{p : n ≤ m}} → Expr Σ n k → Expr Σ m k
weaken^ = weaken^'

weaken^A : {Σ : Signature} {ar : _} {n m : ℕ} {{p : n ≤ m}} → Args Σ n ar → Args Σ m ar
weaken^A = weaken^A'


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
  _,_ : {m : ℕ} → DepCtx Σ n m → TyExpr Σ (m + n) → DepCtx Σ n (suc m)

{-
Extraction of types from contexts.
We need this partial version instead of the total well-typed one (below, not used).
-}

get : {Σ : Signature} {n : ℕ} (k : ℕ) → Ctx Σ n → Partial (VarPos n × TyExpr Σ n)
get k ◇ = fail
get zero (Γ , A) = return (last , weakenL A)
get (suc k) (Γ , X) = do
  (k' , A) ← get k Γ
  return (prev k' , weakenL A)

getTotal : {Σ : Signature} {n : ℕ} (k : VarPos n) → Ctx Σ n → TyExpr Σ n
getTotal last (Γ , A) = weakenL A
getTotal (prev k) (Γ , X) = weakenL (getTotal k Γ)


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

liftSig : {n m : ℕ} {Σ Σ' : Signature} {{p : n ≤ m}} → (Σ →Sig Σ') n → (Σ →Sig Σ') m
(liftSig ↑ $ s) x = (↑ $ s) x

{- Lifting of a map between signatures to expressions -}

↑Expr : {Σ Σ' : Signature} {n : ℕ} {k : SyntaxSort} → (Σ →Sig Σ') n → Expr Σ n k → Expr Σ' n k
↑Args : {Σ Σ' : Signature} {n : ℕ} {args : SyntaxArityArgs} → (Σ →Sig Σ') n → Args Σ n args → Args Σ' n args

↑Expr ↑ (var x) = var x
↑Expr ↑ (sym s x) = (↑ $ s) (↑Args ↑ x)

↑Args ↑ [] = []
↑Args ↑ (es , e) = ↑Args ↑ es , ↑Expr (liftSig ↑) e


{- Arities of metavariables -}

MArityArgs : ℕ → SyntaxArityArgs
MArityArgs zero = []
MArityArgs (suc n) = MArityArgs n , (0 , Tm)

MArity : ℕ → SyntaxSort → SyntaxArity
args (MArity n k) = MArityArgs n
sort (MArity n k) = k


{-
[ExtSig Σ ar] extends the signature [Σ] by an arity [ar].
In order to add a symbol only at the correct arity, we use an inductive family (another possibility
would be to use decidable equality of arities but that would be very ugly).
-}

data ExtSigSymbols (S : SyntaxArity → Set) (ar : SyntaxArity) : SyntaxArity → Set where
  prev : {ar' : SyntaxArity} → S ar' → ExtSigSymbols S ar ar'
  new : ExtSigSymbols S ar ar

ExtSig : Signature → SyntaxArity → Signature
Symbols (ExtSig Σ ar) = ExtSigSymbols (Symbols Σ) ar

{- If an extended signature maps to [Σ'], then the original signature too. -}
Ext→ : {Σ Σ' : Signature} {ar : SyntaxArity} {n : ℕ} → (ExtSig Σ ar →Sig Σ') n → (Σ →Sig Σ') n
Ext→ ↑ $ s = ↑ $ (prev s)

{- [ExtSig^ Σ args] extends the signature [Σ] by symbols for metavariables with arities given by [args] -}

ExtSig^ : Signature → SyntaxArityArgs → Signature
ExtSig^ Σ [] = Σ
ExtSig^ Σ (args , (n , k)) = ExtSig (ExtSig^ Σ args) (MArity n k)


{-
Given two signatures [Σ] and [Σ'], we can map from a signature extended over [Σ] to [Σ'] as long as
we can map from [Σ] to [Σ'] and that we have terms [as] in [Σ'] to replace the new symbols.
[SubstM ↑ as] represents that map.
-}

{- TODO -}
postulate
  Subst1  : {Σ : Signature} {n : ℕ} (m : VarPos (suc n)) {k : SyntaxSort} → Expr Σ (suc n) k → TmExpr Σ (suc n -VarPos m) → Expr Σ n k
  Subst1A : {Σ : Signature} {n : ℕ} (m : VarPos (suc n)) {args : SyntaxArityArgs} → Args Σ (suc n) args → TmExpr Σ (suc n -VarPos m) → Args Σ n args

-- Subst1 last (var last) a = {!a!}
-- Subst1 (prev m) (var last) a = {!!}
-- Subst1 m (var (prev x)) a = {!!}
-- Subst1 m (sym s x) a = sym s (Subst1A m x a)

-- Subst1A m [] a = []
-- Subst1A m (as , x) a = (Subst1A m as a , Subst1 {!m!} x a)

Subst : {Σ : Signature} {m n : ℕ} {k : SyntaxSort} → Expr Σ (m + n) k → Args Σ n (MArityArgs m) → Expr Σ n k
Subst {m = zero} e [] = e
Subst {m = suc m} e (as , a) = Subst (Subst1 last e (weaken^ a)) as

SubstM : {Σ Σ' : Signature} {m : ℕ} {args : SyntaxArityArgs}
      → (Σ →Sig Σ') m
      → Args Σ' m args
      → ((ExtSig^ Σ args) →Sig Σ') m
SubstM ↑ [] = ↑
SubstM ↑ (as , a) $ prev s = SubstM ↑ as $ s
(SubstM ↑ (as , a) $ new) bs = Subst (weaken^' a) bs
