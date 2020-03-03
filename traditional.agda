{-# OPTIONS --rewriting --prop #-}

open import common hiding ([_]; _===_)

{- Syntax of term- and type-expressions, using de Bruijn indices -}

variable
  {n} {m} {k} : ℕ

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

weakenV : {n : ℕ} (p : WeakPos n) → VarPos n → VarPos (suc n)
weakenV last x = prev x
weakenV (prev p) last = last
weakenV (prev p) (prev x) = prev (weakenV p x)

weaken : {n : ℕ} {k : SyntaxSort} (p : WeakPos n) → Expr k n → Expr k (suc n)
weaken p uu = uu
weaken p (el v) = el (weaken p v)
weaken p (pi A B) = pi (weaken p A) (weaken (prev p) B)
weaken p (var x) = var (weakenV p x)
weaken p (lam A B u) = lam (weaken p A) (weaken (prev p) B) (weaken (prev p) u)
weaken p (app A B f a) = app (weaken p A) (weaken (prev p) B) (weaken p f) (weaken p a)

data Mor (n m : ℕ) : ℕ → Set where 
 ◇ : Mor n m 0
 _,_ : {k : ℕ} (δ : Mor n m k) (u : TmExpr (n + m)) → Mor n m (suc k)

weakenMor : Mor n m k → Mor n (suc m) k
weakenMor ◇ = ◇
weakenMor (δ , u) = (weakenMor δ , weaken last u)

weakenMor+ : Mor n m k → Mor n (suc m) (suc k)
weakenMor+ δ = weakenMor δ , var last

weakV : {n m : ℕ} → VarPos n → VarPos (n + m)
weakV {m = zero} x = x
weakV {m = suc m} x = prev (weakV x)

infix 30 _[_]

_[_] : {p : SyntaxSort} (A : Expr p (n + k)) (δ : Mor n m k) → Expr p (n + m)

uu [ δ ] = uu
el v [ δ ] = el (v [ δ ])
pi A B [ δ ] = pi (A [ δ ]) (B [ weakenMor+ δ ])

var x [ ◇ ] = var (weakV x)
var last [ δ , u ] = u
var (prev x) [ δ , u ] = var x [ δ ]
lam A B u [ δ ] = lam (A [ δ ]) (B [ weakenMor+ δ ]) (u [ weakenMor+ δ ])
app A B f a [ δ ] = app (A [ δ ]) (B [ weakenMor+ δ ]) (f [ δ ]) (a [ δ ])

subst : {n : ℕ} {k : SyntaxSort} → Expr k (suc n) → TmExpr n → Expr k n
subst e a = e [ ◇ , a ]

get : {n : ℕ} → VarPos n → Ctx n → TyExpr n
get last (Γ , A) = weaken last A
get (prev k) (Γ , A) = weaken last (get k Γ)

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
    → Derivable (Γ ⊢ A == B)→ Derivable (Γ ⊢ B == C) → Derivable (Γ ⊢ A == C)

  -- Symmetry and transitivity for terms
  TmRefl : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {u : TmExpr n}
    → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u == u :> A)
  TmSymm : {n : ℕ} {Γ : Ctx n} {u v : TmExpr n} {A : TyExpr n}
    → Derivable (Γ ⊢ u == v :> A) → Derivable (Γ ⊢ v == u :> A)
  TmTran : {n : ℕ} {Γ : Ctx n} {u v w : TmExpr n} {A : TyExpr n}
    → Derivable (Γ ⊢ u == v :> A)→ Derivable (Γ ⊢ v == w :> A) → Derivable (Γ ⊢ u == w :> A)

  -- Conversion rules
  Conv : {n : ℕ} {Γ : Ctx n} {u : TmExpr n} {A B : TyExpr n}
    → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ u :> B)
  ConvEq : {n : ℕ} {Γ : Ctx n} {u u' : TmExpr n} {A B : TyExpr n}
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
    → {- Derivable (Γ ⊢ v :> uu) → Derivable (Γ ⊢ v' :> uu) → -} Derivable (Γ ⊢ v == v' :> uu) → Derivable (Γ ⊢ el v == el v')

  -- Rules for Pi
  Pi : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ pi A B)
  PiCong : {n : ℕ} {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)}
    → {- Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A') → -} Derivable (Γ ⊢ A == A') → {- Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A') ⊢ B') → -} Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ pi A B == pi A' B')

  -- Rules for lambda
  Lam : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B)
    → Derivable (Γ ⊢ lam A B u :> pi A B)
  LamCong : {n : ℕ} {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u u' : TmExpr (suc n)}
    → {- Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A') → -} Derivable (Γ ⊢ A == A')
    → {- Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A') ⊢ B') → -} Derivable ((Γ , A) ⊢ B == B')
    → {- Derivable ((Γ , A) ⊢ u :> B) → Derivable ((Γ , A') ⊢ u' :> B') → -} Derivable ((Γ , A) ⊢ u == u' :> B)
    → Derivable (Γ ⊢ lam A B u == lam A' B' u' :> pi A B)

  -- Rules for app
  App : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {f a : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ f :> pi A B) → Derivable (Γ ⊢ a :> A)
    → Derivable (Γ ⊢ app A B f a :> subst B a)
  AppCong : {n : ℕ} {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {f f' a a' : TmExpr n}
    → {- Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A') → -} Derivable (Γ ⊢ A == A')
    → {- Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A') ⊢ B') → -} Derivable ((Γ , A) ⊢ B == B')
    → {- Derivable (Γ ⊢ f :> pi A B) → Derivable (Γ ⊢ f' :> pi A' B') → -} Derivable (Γ ⊢ f == f' :> pi A B)
    → {- Derivable (Γ ⊢ a :> A) → Derivable (Γ ⊢ a' :> A') → -} Derivable (Γ ⊢ a == a' :> A)
    → Derivable (Γ ⊢ app A B f a == app A' B' f' a' :> subst B a)

  -- Equality rules
  BetaPi : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)} {a : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B) → Derivable (Γ ⊢ a :> A)
    → Derivable (Γ ⊢ app A B (lam A B u) a == subst u a :> subst B a)
  -- EtaPi : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {f : TmExpr n}
  --   → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ f :> pi A B)
  --   → Derivable (Γ ⊢ f == lam A B (app (weaken A) {!weaken' (prev last) B!} (weaken f) (var last)) :> pi A B)

data DepCtx (n : ℕ) : ℕ → Set where
  ◇ : DepCtx n 0
  _,_ : {m : ℕ} → DepCtx n m → TyExpr (n + m) → DepCtx n (suc m)

_++_ : {n m : ℕ} → Ctx n → DepCtx n m → Ctx (n + m)
Γ ++ ◇ = Γ
Γ ++ (Δ , A) = (Γ ++ Δ) , A

infixl 30 _++_

data _⊢_===_ (Γ : Ctx n) : DepCtx n m → DepCtx n m → Prop where
  tt : Γ ⊢ ◇ === ◇
  _,_ : {Δ Δ' : DepCtx n m} {A A' : TyExpr (n + m)} → (Γ ⊢ Δ === Δ') → Derivable ((Γ ++ Δ) ⊢ A == A') → Γ ⊢ (Δ , A) === (Δ' , A')


data _⊢_∷>_⇒_ (Γ : Ctx n) : Mor n m k → DepCtx n m → DepCtx n k → Prop where
  tt : {Δ : DepCtx n m} → Γ ⊢ ◇ ∷> Δ ⇒ ◇
  _,_ : {Δ : DepCtx n m} {Δ' : DepCtx n k} {δ : Mor n m k} {u : TmExpr (n + m)} {A : TyExpr (n + k)}
      → Γ ⊢ δ ∷> Δ ⇒ Δ'
      → Derivable (Γ ++ Δ ⊢ u :> (A [ δ ]))
      → Γ ⊢ (δ , u) ∷> Δ ⇒ (Δ' , A)

_-WeakPos_ : (n : ℕ) → WeakPos n → ℕ
n -WeakPos last = n
suc n -WeakPos prev k = n -WeakPos k

weakenCtx : (k : WeakPos n) (Γ : Ctx n) (T : TyExpr (n -WeakPos k)) → Ctx (suc n)
weakenCtx last Γ T = Γ , T
weakenCtx (prev k) (Γ , A) T = weakenCtx k Γ T , weaken k A 

-- WeakTy : {k : WeakPos n} {Γ : Ctx n} {T : TyExpr (n -WeakPos k)} {A : TyExpr n}
--      → Derivable (Γ ⊢ A) → Derivable (weakenCtx k Γ T ⊢ weaken k A)
-- WeakTy= : {k : WeakPos n} {Γ : Ctx n} {T : TyExpr (n -WeakPos k)} {A B : TyExpr n}
--      → Derivable (Γ ⊢ A == B) → Derivable (weakenCtx k Γ T ⊢ weaken k A == weaken k B)
-- WeakTm : {k : WeakPos n} {Γ : Ctx n} {T : TyExpr (n -WeakPos k)} {u : TmExpr n} {A : TyExpr n}
--      → Derivable (Γ ⊢ u :> A) → Derivable (weakenCtx k Γ T ⊢ weaken k u :> weaken k A)
-- WeakTm= : {k : WeakPos n} {Γ : Ctx n} {T : TyExpr (n -WeakPos k)} {u v : TmExpr n} {A : TyExpr n}
--      → Derivable (Γ ⊢ u == v :> A) → Derivable (weakenCtx k Γ T ⊢ weaken k u == weaken k v :> weaken k A)

-- WeakTy UU = UU
-- WeakTy (El dv) = El (WeakTm dv)
-- WeakTy (Pi dA dB) = Pi (WeakTy dA) (WeakTy dB)

-- WeakTy= (TyRefl dA) = TyRefl (WeakTy dA)
-- WeakTy= (TySymm dA=) = TySymm (WeakTy= dA=)
-- WeakTy= (TyTran dA= dB=) = TyTran (WeakTy= dA=) (WeakTy= dB=)
-- WeakTy= UUCong = UUCong
-- WeakTy= (ElCong dv dv' dv=) = ElCong (WeakTm dv) (WeakTm dv') (WeakTm= dv=)
-- WeakTy= (PiCong dA dA' dA= dB dB' dB=) = PiCong (WeakTy dA) (WeakTy dA') (WeakTy= dA=) (WeakTy dB) (WeakTy dB') (WeakTy= dB=)

-- WeakTm (Var k dA) = Conv (Var (weakenV _ k) {!!}) {!!}
-- WeakTm (Conv du dA=) = Conv (WeakTm du) (WeakTy= dA=)
-- WeakTm (Lam dA dB du) = Lam (WeakTy dA) (WeakTy dB) (WeakTm du)
-- WeakTm (App dA dB df da) = Conv (App (WeakTy dA) (WeakTy dB) (WeakTm df) (WeakTm da)) {!!}

-- WeakTm= (TmRefl du) = TmRefl (WeakTm du)
-- WeakTm= (TmSymm du=) = TmSymm (WeakTm= du=)
-- WeakTm= (TmTran du= dv=) = TmTran (WeakTm= du=) (WeakTm= dv=)
-- WeakTm= (ConvEq du= dA=) = ConvEq (WeakTm= du=) (WeakTy= dA=)
-- WeakTm= (LamCong dA dA' dA= dB dB' dB= du du' du=) = LamCong (WeakTy dA) (WeakTy dA') (WeakTy= dA=) (WeakTy dB) (WeakTy dB') (WeakTy= dB=) (WeakTm du) (WeakTm du') (WeakTm= du=)
-- WeakTm= (AppCong dA dA' dA= dB dB' dB= df df' df= da da' da=) = ConvEq (AppCong (WeakTy dA) (WeakTy dA') (WeakTy= dA=) (WeakTy dB) (WeakTy dB') (WeakTy= dB=) (WeakTm df) (WeakTm df') (WeakTm= df=) (WeakTm da) (WeakTm da') (WeakTm= da=)) {!!}
-- WeakTm= (BetaPi dA dB du da) = ConvEq (TmTran (BetaPi (WeakTy dA) (WeakTy dB) (WeakTm du) (WeakTm da)) {!!}) {!!}

-- WeakMor : {Γ : Ctx n} {Δ : DepCtx n m} {Δ' : DepCtx n k} {T : TyExpr (n + m)} {δ : Mor n m k} → Γ ⊢ δ ∷> Δ ⇒ Δ' → Γ ⊢ weakenMor δ ∷> (Δ , T) ⇒ Δ'
-- WeakMor tt = tt
-- WeakMor (dδ , du) = WeakMor dδ , Conv (WeakTm du) {!!}

-- SubstTy : {Γ : Ctx n} {Δ : DepCtx n m} {Δ' : DepCtx n k} {A : TyExpr (n + k)} {δ : Mor n m k}
--        → Derivable (Γ ++ Δ' ⊢ A) → Γ ⊢ δ ∷> Δ ⇒ Δ' → Derivable (Γ ++ Δ ⊢ A [ δ ])
-- SubstTy= : {Γ : Ctx n} {Δ : DepCtx n m} {Δ' : DepCtx n k} {A A' : TyExpr (n + k)} {δ : Mor n m k}
--        → Derivable (Γ ++ Δ' ⊢ A) → Derivable (Γ ++ Δ' ⊢ A == A') → Γ ⊢ δ ∷> Δ ⇒ Δ' → Derivable (Γ ++ Δ ⊢ A [ δ ] == A' [ δ ])
-- SubstTm : {Γ : Ctx n} {Δ : DepCtx n m} {Δ' : DepCtx n k} {u : TmExpr (n + k)} {A : TyExpr (n + k)} {δ : Mor n m k}
--        → Derivable (Γ ++ Δ' ⊢ u :> A) → Γ ⊢ δ ∷> Δ ⇒ Δ' → Derivable (Γ ++ Δ ⊢ u [ δ ] :> A [ δ ])
-- SubstTm= : {Γ : Ctx n} {Δ : DepCtx n m} {Δ' : DepCtx n k} {u u' : TmExpr (n + k)} {A : TyExpr (n + k)} {δ : Mor n m k}
--        → Derivable (Γ ++ Δ' ⊢ u == u' :> A) → Γ ⊢ δ ∷> Δ ⇒ Δ' → Derivable (Γ ++ Δ ⊢ u [ δ ] == u' [ δ ] :> A [ δ ])

-- WeakMor+ : {Γ : Ctx n} {Δ : DepCtx n m} {Δ' : DepCtx n k} {A : TyExpr (n + k)} {δ : Mor n m k} → Derivable (Γ ++ Δ' ⊢ A) → Γ ⊢ δ ∷> Δ ⇒ Δ' → Γ ⊢ weakenMor+ δ ∷> (Δ , A [ δ ]) ⇒ (Δ' , A)
-- WeakMor+ dA dδ = WeakMor dδ , Conv (Var last (WeakTy (SubstTy dA dδ))) {!syntx!}

-- TyEqTy1 : {Γ : Ctx n} {A B : TyExpr n} → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ A)
-- TyEqTy2 : {Γ : Ctx n} {A B : TyExpr n} → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B)
-- TmEqTm1 : {Γ : Ctx n} {u u' : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ u :> A)
-- TmEqTm2 : {Γ : Ctx n} {u u' : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ u' :> A)

-- SubstTy UU dδ = UU
-- SubstTy (El dv) dδ = El (SubstTm dv dδ)
-- SubstTy (Pi dA dB) dδ = Pi (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ))

-- -- SubstTy= _ (TyRefl dA) dδ = TyRefl (SubstTy dA dδ)
-- -- SubstTy= dA (TySymm dA=) dδ = TySymm (SubstTy= {!!} dA= dδ)
-- -- SubstTy= dA (TyTran dA= dB=) dδ = TyTran (SubstTy= dA dA= dδ) (SubstTy= {!!} dB= dδ)
-- -- SubstTy= dA UUCong dδ = UUCong
-- -- SubstTy= dA (ElCong dv=) dδ = ElCong (SubstTm= dv= dδ)
-- -- SubstTy= {Γ = Γ} (Pi dA dB) (PiCong dA= dB=) dδ = PiCong (SubstTy= dA dA= dδ) (SubstTy= dB dB= (WeakMor+ dA dδ))

-- -- SubstTm (Var k du) dδ = {!!}
-- -- SubstTm (Conv du dA=) dδ = Conv (SubstTm du dδ) (SubstTy= dA= dδ)
-- -- SubstTm (Lam dA dB du) dδ = Lam (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm du (WeakMor+ dA dδ))
-- -- SubstTm (App dA dB df da) dδ = Conv (App (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm df dδ) (SubstTm da dδ)) {!!}

-- -- SubstTm= (TmRefl du) dδ = TmRefl (SubstTm du dδ)
-- -- SubstTm= (TmSymm du=) dδ = TmSymm (SubstTm= du= dδ)
-- -- SubstTm= (TmTran du= dv=) dδ = TmTran (SubstTm= du= dδ) (SubstTm= dv= dδ)
-- -- SubstTm= (ConvEq du= dA=) dδ = ConvEq (SubstTm= du= dδ) (SubstTy= dA= dδ)
-- -- SubstTm= (LamCong dA= dB= du=) dδ = LamCong (SubstTy= dA= dδ) (SubstTy= dB= (WeakMor+ {!TyEqTy1 dA=!} dδ)) (SubstTm= du= (WeakMor+ {!TyEqTy1 dA=!} dδ))
-- -- SubstTm= (AppCong dA= dB= df= da=) dδ = ConvEq (AppCong (SubstTy= dA= dδ) (SubstTy= dB= (WeakMor+ {!TyEqTy1 dA=!} dδ)) (SubstTm= df= dδ) (SubstTm= da= dδ)) {!stx!}
-- -- SubstTm= (BetaPi dA dB du da) dδ = ConvEq (TmTran (BetaPi (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm du (WeakMor+ dA dδ)) (SubstTm da dδ)) {!!}) {!!}

-- -- ConvTy  : {n m : ℕ} {Γ : Ctx n} {Δ Δ' : DepCtx n m} {A : TyExpr (n + m)} → Derivable ((Γ ++ Δ) ⊢ A) → (Γ ⊢ Δ === Δ') → Derivable ((Γ ++ Δ') ⊢ A)
-- -- ConvTy= : {n m : ℕ} {Γ : Ctx n} {Δ Δ' : DepCtx n m} {A A' : TyExpr (n + m)} → Derivable ((Γ ++ Δ) ⊢ A == A') → (Γ ⊢ Δ === Δ') → Derivable ((Γ ++ Δ') ⊢ A == A')
-- -- ConvTm  : {n m : ℕ} {Γ : Ctx n} {Δ Δ' : DepCtx n m} {A : TyExpr (n + m)} {u : TmExpr (n + m)} → Derivable ((Γ ++ Δ) ⊢ u :> A) → (Γ ⊢ Δ === Δ') → Derivable ((Γ ++ Δ') ⊢ u :> A)
-- -- ConvTm= : {n m : ℕ} {Γ : Ctx n} {Δ Δ' : DepCtx n m} {A : TyExpr (n + m)} {u u' : TmExpr (n + m)} → Derivable ((Γ ++ Δ) ⊢ u == u' :> A) → (Γ ⊢ Δ === Δ') → Derivable ((Γ ++ Δ') ⊢ u == u' :> A)


-- -- ConvTy UU dΔ= = UU
-- -- ConvTy (El dv) dΔ= = El (ConvTm dv dΔ=)
-- -- ConvTy (Pi dA dB) dΔ= = Pi (ConvTy dA dΔ=) (ConvTy dB (dΔ= , TyRefl dA))

-- -- ConvTy= (TyRefl dA) dΔ= = TyRefl (ConvTy dA dΔ=)
-- -- ConvTy= (TySymm dA=) dΔ= = TySymm (ConvTy= dA= dΔ=)
-- -- ConvTy= (TyTran dA= dB=) dΔ= = TyTran (ConvTy= dA= dΔ=) (ConvTy= dB= dΔ=)
-- -- ConvTy= UUCong dΔ= = UUCong
-- -- ConvTy= (ElCong dv=) dΔ= = ElCong (ConvTm= dv= dΔ=)
-- -- ConvTy= (PiCong dA= dB=) dΔ= = PiCong (ConvTy= dA= dΔ=) (ConvTy= dB= (dΔ= , {!ok!}))

-- -- ConvTm (Var k du) dΔ= = Conv (Var k (ConvTy {!TODO!} dΔ=)) {!TODO!}
-- -- ConvTm (Conv du dA=) dΔ= = Conv (ConvTm du dΔ=) (ConvTy= dA= dΔ=)
-- -- ConvTm (Lam dA dB du) dΔ= = Lam (ConvTy dA dΔ=) (ConvTy dB (dΔ= , TyRefl dA)) (ConvTm du (dΔ= , TyRefl dA))
-- -- ConvTm (App dA dB df da) dΔ= = App (ConvTy dA dΔ=) (ConvTy dB (dΔ= , TyRefl dA)) (ConvTm df dΔ=) (ConvTm da dΔ=)

-- -- ConvTm= (TmRefl du) dΔ= = TmRefl (ConvTm du dΔ=)
-- -- ConvTm= (TmSymm du=) dΔ= = TmSymm (ConvTm= du= dΔ=)
-- -- ConvTm= (TmTran du= dv=) dΔ= = TmTran (ConvTm= du= dΔ=) (ConvTm= dv= dΔ=)
-- -- ConvTm= (ConvEq du= dA=) dΔ= = ConvEq (ConvTm= du= dΔ=) (ConvTy= dA= dΔ=)
-- -- ConvTm= (LamCong dA= dB= du=) dΔ= = LamCong (ConvTy= dA= dΔ=) (ConvTy= dB= (dΔ= , {!ok!})) (ConvTm= du= (dΔ= , {!ok!}))
-- -- ConvTm= (AppCong dA= dB= df= da=) dΔ= = AppCong (ConvTy= dA= dΔ=) (ConvTy= dB= (dΔ= , {!ok!})) (ConvTm= df= dΔ=) (ConvTm= da= dΔ=)
-- -- ConvTm= (BetaPi dA dB du da) dΔ= = BetaPi (ConvTy dA dΔ=) (ConvTy dB (dΔ= , TyRefl dA)) (ConvTm du (dΔ= , TyRefl dA)) (ConvTm da dΔ=)

-- -- TyEqTy1 (TyRefl dA) = dA
-- -- TyEqTy1 (TySymm dA=) = TyEqTy2 dA=
-- -- TyEqTy1 (TyTran dA= dB=) = TyEqTy1 dA=
-- -- TyEqTy1 UUCong = UU
-- -- TyEqTy1 (ElCong du=) = El (TmEqTm1 du=)
-- -- TyEqTy1 (PiCong dA= dB=) = Pi (TyEqTy1 dA=) (TyEqTy1 dB=)

-- -- TyEqTy2 (TyRefl dA) = dA
-- -- TyEqTy2 (TySymm dA=) = TyEqTy1 dA=
-- -- TyEqTy2 (TyTran dA= dB=) = TyEqTy2 dB=
-- -- TyEqTy2 UUCong = UU
-- -- TyEqTy2 (ElCong du=) = El (TmEqTm2 du=)
-- -- TyEqTy2 (PiCong dA= dB=) = Pi (TyEqTy2 dA=) (ConvTy (TyEqTy2 dB=) (tt , dA=))

-- -- TmEqTm1 (TmRefl du) = du
-- -- TmEqTm1 (TmSymm du=) = TmEqTm2 du=
-- -- TmEqTm1 (TmTran du= dv=) = TmEqTm1 du=
-- -- TmEqTm1 (ConvEq du= dA=) = Conv (TmEqTm1 du=) dA=
-- -- TmEqTm1 (LamCong dA= dB= du=) = Lam (TyEqTy1 dA=) (TyEqTy1 dB=) (TmEqTm1 du=)
-- -- TmEqTm1 (AppCong dA= dB= df= da=) = App (TyEqTy1 dA=) (TyEqTy1 dB=) (TmEqTm1 df=) (TmEqTm1 da=)
-- -- TmEqTm1 (BetaPi dA dB du da) = App dA dB (Lam dA dB du) da

-- -- TmEqTm2 (TmRefl du) = du
-- -- TmEqTm2 (TmSymm du=) = TmEqTm1 du=
-- -- TmEqTm2 (TmTran du= dv=) = TmEqTm2 dv=
-- -- TmEqTm2 (ConvEq du= dA=) = Conv (TmEqTm2 du=) dA=
-- -- TmEqTm2 (LamCong dA= dB= du=) = Conv (Lam (TyEqTy2 dA=) (ConvTy (TyEqTy2 dB=) (tt , dA=)) (ConvTm (Conv (TmEqTm2 du=) dB=) (tt , dA=))) (PiCong (TySymm dA=) (ConvTy= (TySymm dB=) (tt , dA=)))
-- -- TmEqTm2 (AppCong dA= dB= df= da=) = Conv (App (TyEqTy2 dA=) (ConvTy (TyEqTy2 dB=) (tt , dA=)) (Conv (TmEqTm2 df=) (PiCong dA= dB=)) (Conv (TmEqTm2 da=) dA=)) {!TySymm (SubstTy= dB= (tt , {!da=!}))!}
-- -- TmEqTm2 (BetaPi dA dB du da) = {!SubstTm du (tt , {!da!})!}
