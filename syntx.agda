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
  _∷_ : (ℕ × Sort) → ArityArgs Sort → ArityArgs Sort

record Arity (Sort : Set) : Set where
  constructor mkarity
  field
    args : ArityArgs Sort
    sort : Sort
open Arity public

{- This is the sorts that we use for the syntax, two sorts: types and terms -}

data SyntaxSort : Set where
  Ty : SyntaxSort
  Tm : SyntaxSort

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
  _∷_ : {m : ℕ} {k : SyntaxSort} {args : SyntaxArityArgs}
      → Expr Σ (m + n) k → Args Σ n args
      → Args Σ n ((m , k) ∷ args)

{- Abbreviations for type-/term-expressions -}

TyExpr : (Σ : Signature) → ℕ → Set
TyExpr Σ n = Expr Σ n Ty

TmExpr : (Σ : Signature) → ℕ → Set
TmExpr Σ n = Expr Σ n Tm

{- Weakening -}

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
weakenA (e ∷ args) k = weaken e (weakenWeakPos _ k) ∷ weakenA args k

weakenL : {Σ : Signature} {n : ℕ} {k : SyntaxSort} → Expr Σ n k → Expr Σ (suc n) k
weakenL e = weaken e last

weaken^ : {Σ : Signature} {k : _} {n : ℕ} → Expr Σ 0 k → Expr Σ n k
weaken^ {n = zero} e = e
weaken^ {n = suc n} e = weakenL (weaken^ e)

postulate
  weaken≤ : {Σ : Signature} {k : _} {n m : ℕ} {{_ : n ≤ m}} → Expr Σ n k → Expr Σ m k

{- Contexts, [Ctx Σ n] represents contexts in signature [Σ] and of length [n] -}

data Ctx (Σ : Signature) : ℕ → Set where
  ◇ : Ctx Σ 0
  _,_ : {n : ℕ} (Γ : Ctx Σ n) (A : TyExpr Σ n) → Ctx Σ (suc n)

{-
Dependent contexts, [DepCtx Σ n m] represents contexts in signature [Σ], in scope [n], and of
length [m]. They are built in the other direction compared to [Ctx], we add types to the left
instead of adding them to the right. The reason is that the "purpose" of dependent contexts is to
move the types one by one to the context on the left.
-}

data DepCtx (Σ : Signature) (n : ℕ) : ℕ → Set where
  ◇ : DepCtx Σ n 0
  _,_ : {m : ℕ} (A : TyExpr Σ n) → DepCtx Σ (suc n) m → DepCtx Σ n (suc m)

{-
Extraction of types from contexts.
We need this partial version instead of the total well-typed one (below, not used).
-}

get : {Σ : Signature} {n : ℕ} (k : ℕ) → Ctx Σ n → Partial (Lift (VarPos n × TyExpr Σ n))
get k ◇ = fail
get zero (Γ , A) = return (lift (last , weakenL A))
get (suc k) (Γ , X) = do
  (lift (k' , A)) ← get k Γ
  return (lift (prev k' , weakenL A))

getTotal : {Σ : Signature} {n : ℕ} (k : VarPos n) → Ctx Σ n → TyExpr Σ n
getTotal last (Γ , A) = weakenL A
getTotal (prev k) (Γ , X) = weakenL (getTotal k Γ)
