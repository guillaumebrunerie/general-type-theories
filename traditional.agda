{-# OPTIONS --rewriting --prop #-}

open import common

{- Syntax of term- and type-expressions, using de Bruijn indices -}

data Expr : SyntaxSort → ℕ → Set

TyExpr = Expr Ty
TmExpr = Expr Tm

data Expr where
  uu : {n : ℕ} → TyExpr n
  el : {n : ℕ} (v : TmExpr n) → TyExpr n
  pi : {n : ℕ} (A : TyExpr n) (B : TyExpr (suc n)) → TyExpr n

  var : {n : ℕ} (x : VarPos n) → TmExpr n
  lam : {n : ℕ} (A : TyExpr n) (B : TyExpr (suc n)) (u : TmExpr (suc n)) → TmExpr n
  app : {n : ℕ} (A : TyExpr n) (B : TyExpr (suc n)) (f : TmExpr n) (a : TmExpr n) → TmExpr n

data Ctx : ℕ → Set where
  ◇ : Ctx 0
  _,_ : {n : ℕ} (Γ : Ctx n) (A : TyExpr n) → Ctx (suc n)

{- The four different forms of (pre)judgments. -}

data Judgment : Set where
  _⊢_ : {n : ℕ} (Γ : Ctx n) → TyExpr n → Judgment
  _⊢_:>_ : {n : ℕ} (Γ : Ctx n) → TmExpr n → TyExpr n → Judgment
  _⊢_==_ : {n : ℕ} (Γ : Ctx n) → TyExpr n → TyExpr n → Judgment
  _⊢_==_:>_ : {n : ℕ} (Γ : Ctx n) → TmExpr n → TmExpr n → TyExpr n → Judgment

postulate
  weaken : {n : ℕ} {k : SyntaxSort} → Expr k n → Expr k (suc n)
  subst : {n : ℕ} {k : SyntaxSort} → Expr k (suc n) → TmExpr n → Expr k n

get : {n : ℕ} → VarPos n → Ctx n → TyExpr n
get last (Γ , A) = weaken A
get (prev k) (Γ , A) = weaken (get k Γ)

{- Derivability of judgments, the typing rules of the type theory -}

data Derivable : Judgment → Prop where

  -- Variable rules
  Var : {n : ℕ} {Γ : Ctx n} (k : VarPos n)
    → Derivable (Γ ⊢ get k Γ)
    → Derivable (Γ ⊢ var k :> get k Γ)

  -- Symmetry and transitivity for types
  TyRefl : {n : ℕ} {Γ : Ctx n} {A : TyExpr n}
    → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A == A)
  TySymm : {n : ℕ} {Γ : Ctx n} {A B : TyExpr n}
    → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B == A)
  TyTran : {n : ℕ} {Γ : Ctx n} {A B C : TyExpr n}
    → Derivable (Γ ⊢ B) → Derivable (Γ ⊢ A == B)→ Derivable (Γ ⊢ B == C) → Derivable (Γ ⊢ A == C)

  -- Symmetry and transitivity for terms
  TmRefl : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {u : TmExpr n}
    → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u == u :> A)
  TmSymm : {n : ℕ} {Γ : Ctx n} {u v : TmExpr n} {A : TyExpr n}
    → Derivable (Γ ⊢ u == v :> A) → Derivable (Γ ⊢ v == u :> A)
  TmTran : {n : ℕ} {Γ : Ctx n} {u v w : TmExpr n} {A : TyExpr n}
    → Derivable (Γ ⊢ v :> A) → Derivable (Γ ⊢ u == v :> A)→ Derivable (Γ ⊢ v == w :> A) → Derivable (Γ ⊢ u == w :> A)

  -- Conversion rules
  Conv : {n : ℕ} {Γ : Ctx n} {u : TmExpr n} {A B : TyExpr n} → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ u :> B)
  ConvEq : {n : ℕ} {Γ : Ctx n} {u u' : TmExpr n} {A B : TyExpr n} → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ u == u' :> B)


  -- Rules for UU
  UU : {n : ℕ} {Γ : Ctx n}
    → Derivable (Γ ⊢ uu)
  UUCong : {n : ℕ} {Γ : Ctx n}
    → Derivable (Γ ⊢ uu == uu)

  -- Rules for El
  El : {n : ℕ} {Γ : Ctx n} {v : TmExpr n}
    → Derivable (Γ ⊢ v :> uu) → Derivable (Γ ⊢ el v)
  ElCong : {n : ℕ} {Γ : Ctx n} {v v' : TmExpr n}
    → Derivable (Γ ⊢ v == v' :> uu) → Derivable (Γ ⊢ el v == el v')

  -- Rules for Pi
  Pi : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ pi A B)
  PiCong : {n : ℕ} {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)}
    → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ pi A B == pi A' B')

  -- Rules for lambda
  Lam : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B)
    → Derivable (Γ ⊢ lam A B u :> pi A B)
  LamCong : {n : ℕ} {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u u' : TmExpr (suc n)}
    → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable ((Γ , A) ⊢ u == u' :> B)
    → Derivable (Γ ⊢ lam A B u == lam A' B' u' :> pi A B)

  -- Rules for app
  App : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {f a : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ f :> pi A B) → Derivable (Γ ⊢ a :> A)
    → Derivable (Γ ⊢ app A B f a :> subst B a)
  AppCong : {n : ℕ} {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {f f' a a' : TmExpr n}
    → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ f == f' :> pi A B) → Derivable (Γ ⊢ a == a' :> A)
    → Derivable (Γ ⊢ app A B f a == app A' B' f' a' :> subst B a)

  -- Equality rules
  BetaPi : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)} {a : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B) → Derivable (Γ ⊢ a :> A)
    → Derivable (Γ ⊢ app A B (lam A B u) a == subst u a :> subst B a)
  -- EtaPi : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {f : TmExpr n}
  --   → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ f :> pi A B)
  --   → Derivable (Γ ⊢ f == lam A B (app (weaken A) {!weaken' (prev last) B!} (weaken f) (var last)) :> pi A B)
