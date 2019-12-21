{-# OPTIONS --rewriting --prop #-}

open import common

{- Syntax of term- and type-expressions, using de Bruijn indices -}

data TyExpr : ℕ → Set
data TmExpr : ℕ → Set

data TyExpr where
  nat : {n : ℕ} → TyExpr n

data TmExpr where
  var : {n : ℕ} (x : VarPos n) → TmExpr n
  zero : {n : ℕ} → TmExpr n
  suc : {n : ℕ} (u : TmExpr n) → TmExpr n

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
  weaken : {n : ℕ} → TyExpr n → TyExpr (suc n)

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

  -- Rules for Nat
  Nat : {n : ℕ} {Γ : Ctx n}
    → Derivable (Γ ⊢ nat)
  NatCong : {n : ℕ} {Γ : Ctx n}
    → Derivable (Γ ⊢ nat == nat)

  -- Rules for zero
  Zero : {n : ℕ} {Γ : Ctx n}
    → Derivable (Γ ⊢ zero :> nat)
  ZeroCong : {n : ℕ} {Γ : Ctx n}
    → Derivable (Γ ⊢ zero == zero :> nat)

  -- Rules for suc
  Suc : {n : ℕ} {Γ : Ctx n} {u : TmExpr n}
    → Derivable (Γ ⊢ u :> nat) → Derivable (Γ ⊢ suc u :> nat)
  SucCong : {n : ℕ} {Γ : Ctx n} {u u' : TmExpr n}
    → Derivable (Γ ⊢ u == u' :> nat) → Derivable (Γ ⊢ suc u == suc u' :> nat)
