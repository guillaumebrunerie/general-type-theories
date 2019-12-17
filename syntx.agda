{-# OPTIONS --prop --rewriting #-}

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
A signature consists of symbols, which are indexed by their arities. The other solution to have a
set of symbols and an arity function is very inconvenient for some reason.
-}

record Signature : Set₁ where
  field
    Symbols : SyntaxArity → Set
open Signature public

{-
Expressions are indexed by their syntactic class and their scope-length. An expression is either a
variable or a symbol applied to the appropriate number of arguments.
The type [Expr Σ n] is defined simultaneously with the type [generateArgs Σ n args] which represents
the type of the arguments of a symbol with arity (args, _). 
-}

data Expr (Σ : Signature) (n : ℕ) : SyntaxSort → Set

data generateArgs (Σ : Signature) (n : ℕ) : SyntaxArityArgs → Set where
  [] : generateArgs Σ n []
  _∷_ : {m : ℕ} {k : SyntaxSort} {args : SyntaxArityArgs}
      → Expr Σ (m + n) k → generateArgs Σ n args
      → generateArgs Σ n ((m , k) ∷ args)

data Expr Σ n where
  var : VarPos n → Expr Σ n Tm
  sym : {ar : SyntaxArity} (s : Symbols Σ ar) → generateArgs Σ n (args ar) → Expr Σ n (sort ar)

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

weaken : {Σ : Signature} {n : ℕ} {s : SyntaxSort} → Expr Σ n s → WeakPos n → Expr Σ (suc n) s
weakenA : {Σ : Signature} {n : ℕ} {ar : SyntaxArityArgs} → generateArgs Σ n ar
            → WeakPos n → generateArgs Σ (suc n) ar

weaken (var x) k = var (weakenV x k)
weaken (sym s args) k = sym s (weakenA args k)

weakenA [] k = []
weakenA (e ∷ args) k = weaken e (weakenWeakPos _ k) ∷ weakenA args k

weakenL : {Σ : Signature} {n : ℕ} {s : SyntaxSort} → Expr Σ n s → Expr Σ (suc n) s
weakenL e = weaken e last

weaken^ : {Σ : Signature} {n : ℕ} → TyExpr Σ 0 → TyExpr Σ n
weaken^ {n = zero} e = e
weaken^ {n = suc n} e = weakenL (weaken^ e)

{- Raw contexts -}

data Ctx (Σ : Signature) : ℕ → Set where
  ◇ : Ctx Σ 0
  _,_ : {n : ℕ} (Γ : Ctx Σ n) (A : TyExpr Σ n) → Ctx Σ (suc n)

get : {Σ : Signature} {n : ℕ} (k : VarPos n) → Ctx Σ n → TyExpr Σ n
get last (Γ , A) = weakenL A
get (prev k) (Γ , A) = weakenL (get k Γ)
