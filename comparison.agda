{-# OPTIONS --rewriting --prop #-}

open import common

open import syntx as N
open import derivability as N

open import traditional as T

Σ : Signature
Σ = N.TTSig ΠUEl-TT


{- Maps between expressions -}

T→N : {n : ℕ} {k : SyntaxSort} → T.Expr k n → N.Expr Σ n k
T→N uu = sym 1 []
T→N (el v) = sym 0 ([] , T→N v)
T→N (pi A B) = sym 4 ([] , T→N A , T→N B)
T→N (var x) = var x
T→N (lam A B u) = sym 3 ([] , T→N A , T→N B , T→N u)
T→N (app A B f a) = sym 2 ([] , T→N A , T→N B , T→N f , T→N a)


N→T : {n : ℕ} {k : SyntaxSort} → N.Expr Σ n k → T.Expr k n
N→T (var x) = var x
N→T (sym (prev (prev (prev (prev new)))) ([] , A , B)) = pi (N→T A) (N→T B)
N→T (sym (prev (prev (prev new))) ([] , A , B , u)) = lam (N→T A) (N→T B) (N→T u)
N→T (sym (prev (prev new)) ([] , A , B , f , a)) = app (N→T A) (N→T B) (N→T f) (N→T a)
N→T (sym (prev new) []) = uu
N→T (sym new ([] , v)) = el (N→T v)


{- Equalities -}

TNT : {n : ℕ} {k : SyntaxSort} (e : N.Expr Σ n k) → T→N (N→T e) ≡ e
TNT (var x) = refl
TNT (sym (prev (prev (prev (prev new)))) ([] , A , B)) = ap2 (λ x y → sym 4 ([] , x , y)) (TNT A) (TNT B)
TNT (sym (prev (prev (prev new))) ([] , A , B , u)) = ap3 (λ x y z → sym 3 ([] , x , y , z)) (TNT A) (TNT B) (TNT u)
TNT (sym (prev (prev new)) ([] , A , B , f , a)) = ap4 (λ x y z t → sym 2 ([] , x , y , z , t)) (TNT A) (TNT B) (TNT f) (TNT a)
TNT (sym (prev new) []) = refl
TNT (sym new ([] , v)) = ap (λ v → sym 0 ([] , v)) (TNT v)

NTN : {n : ℕ} {k : SyntaxSort} (e : T.Expr k n) → N→T (T→N e) ≡ e
NTN uu = refl
NTN (el v) = ap el (NTN v)
NTN (pi A B) = ap2 pi (NTN A) (NTN B)
NTN (var x) = refl
NTN (lam A B u) = ap3 lam (NTN A) (NTN B) (NTN u)
NTN (app A B f a) = ap4 app (NTN A) (NTN B) (NTN f) (NTN a)


{- Derivability -}

data NJudgment : Set where
  njudgment : {n : ℕ} (Γ : N.Ctx Σ n) {k : JudgmentSort} → N.Judgment Σ Γ 0 k → NJudgment

NDerivable : NJudgment → Prop
NDerivable (njudgment Γ j) = N.Derivable (TTDer ΠUEl-TT) j

T→NCtx : {n : ℕ} → T.Ctx n → N.Ctx Σ n
T→NCtx ◇ = ◇
T→NCtx (Γ , A) = (T→NCtx Γ , T→N A)

T→NJ : T.Judgment → NJudgment
T→NJ (Γ ⊢ A) = njudgment (T→NCtx Γ) (◇ ⊢ T→N A)
T→NJ (Γ ⊢ u :> A) = njudgment (T→NCtx Γ) (◇ ⊢ T→N u :> T→N A)
T→NJ (Γ ⊢ A == B) = njudgment (T→NCtx Γ) (◇ ⊢ T→N A == T→N B)
T→NJ (Γ ⊢ u == v :> A) = njudgment (T→NCtx Γ) (◇ ⊢ T→N u == T→N v :> T→N A)


T→NDer : {j : T.Judgment} → T.Derivable j → NDerivable (T→NJ j)
T→NDer (Var k d) = apr {!str (var ?)!} {!!}
T→NDer (TyRefl dA) = apr (str tyRefl) ([] , T→NDer dA)
T→NDer (TySymm dA=) = apr (str tySymm) ([] , {!T→NDer dA=!} , {!!} , {!!})
T→NDer (TyTran dA= dB dB=) = {!!}
T→NDer (TmRefl du) = apr (str tmRefl) ([] , T→NDer du)
T→NDer (TmSymm du=) = apr (str tmSymm) ([] , T→NDer du=)
T→NDer (TmTran dv du= dv=) = apr (str tmTran) ([] , T→NDer du= , T→NDer dv=)
T→NDer (Conv d d₁ d₂) = {!!}
T→NDer (ConvEq d d₁ d₂) = {!!}
T→NDer UU = apr 1 []
T→NDer UUCong = {!!}
T→NDer (El dv) = apr 0 ([] , T→NDer dv)
T→NDer (ElCong dv) = {!!}
T→NDer (Pi dA dB) = apr 4 ([] , T→NDer dA , flat {!T→NDer dB!})
T→NDer (PiCong d d₁ d₂) = {!!}
T→NDer (Lam d d₁ d₂) = apr 3 {!!}
T→NDer (LamCong d d₁ d₂ d₃) = {!!}
T→NDer (App dA dB df da) = {!apr 2 ([] , T→NDer dA , flat {j = (◇ , _) ⊢ _} (T→NDer dB) , T→NDer df , T→NDer da)!}
T→NDer (AppCong d d₁ d₂ d₃ d₄) = {!!}
T→NDer (BetaPi d d₁ d₂ d₃) = {!!}


N→TCtx : {n : ℕ} → N.Ctx Σ n → T.Ctx n
N→TCtx ◇ = ◇
N→TCtx (Γ , A) = (N→TCtx Γ , N→T A)

N→TJ : NJudgment → T.Judgment
N→TJ (njudgment Γ (◇ ⊢ A)) = N→TCtx Γ ⊢ N→T A
N→TJ (njudgment Γ (◇ ⊢ u :> A)) = N→TCtx Γ ⊢ N→T u :> N→T A
N→TJ (njudgment Γ (◇ ⊢ A == B)) = N→TCtx Γ ⊢ N→T A == N→T B
N→TJ (njudgment Γ (◇ ⊢ u == v :> A)) = N→TCtx Γ ⊢ N→T u == N→T v :> N→T A

N→TDer : {j : NJudgment} → NDerivable j → T.Derivable (N→TJ j)
N→TDer {njudgment Γ _} (apr r js-der) = {!r!}

-- gDer : {j : NJudgment} → NDerivable j → T.Derivable (gJ j)
-- gDer {njudgment Γ _} (apr typingrule {js = [] , (◇ ⊢ u :> .(sym (prev (prev new)) []))} ([] , du) {{tt , (refl , tt) , tt}}) = Suc (gDer du)
-- gDer {njudgment Γ _} (apr congruencerule {js = [] , (◇ ⊢ u == v :> .(sym (prev (prev new)) []))} ([] , du=) {{tt , (refl , (refl , tt)) , tt}}) = SucCong (gDer du=)
-- gDer {njudgment Γ _} (apr (prev typingrule) {js = []} []) = Zero
-- gDer {njudgment Γ _} (apr (prev congruencerule) {js = []} []) = ZeroCong
-- gDer {njudgment Γ _} (apr (prev (prev typingrule)) {js = []} []) = Nat
-- gDer {njudgment Γ _} (apr (prev (prev congruencerule)) {js = []} []) = NatCong
-- gDer {njudgment Γ _} (apr (prev (prev (prev (var k)))) {js = [] , (◇ ⊢ .(snd (N.get k Γ $ _)))} ([] , dA) {{getIsDef , (refl , tt)}}) = {!Var (fst (N.get k Γ $ getIsDef)) {!gDer dA!}!}
-- gDer {njudgment Γ _} (apr (prev (prev (prev conv))) {js = ([] , (◇ ⊢ u :> A)) , (◇ ⊢ .A == B)} ([] , du , dA=) {{refl , tt}}) = Conv {!!} (gDer du) (gDer dA=)
-- gDer {njudgment Γ _} (apr (prev (prev (prev convEq))) js-der) = {!!}
-- gDer {njudgment Γ _} (apr (prev (prev (prev tyRefl))) {js = [] , (◇ ⊢ A)} ([] , dA)) = TyRefl (gDer dA)
-- gDer {njudgment Γ _} (apr (prev (prev (prev tySymm))) js-der) = {!!}
-- gDer {njudgment Γ _} (apr (prev (prev (prev tyTran))) js-der) = {!!}
-- gDer {njudgment Γ _} (apr (prev (prev (prev tmRefl))) js-der) = {!!}
-- gDer {njudgment Γ _} (apr (prev (prev (prev tmSymm))) {js = [] , (◇ ⊢ u == v :> A)} ([] , du=)) = TmSymm (gDer du=)
-- gDer {njudgment Γ _} (apr (prev (prev (prev tmTran))) js-der) = {!!}
