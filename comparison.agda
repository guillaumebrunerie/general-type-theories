{-# OPTIONS --rewriting --prop #-}

open import common

open import syntx as N
open import derivability as N

open import traditional as T

Σ : Signature
Σ = (ExtSig (ExtSig (ExtSig Σ₀ (MArity 0 Ty)) (MArity 0 Tm)) (MArity 1 Tm))


{- Maps between signatures -}

fTy : {n : ℕ} → T.TyExpr n → N.TyExpr Σ n
fTy nat = sym (prev (prev new)) []

fTm : {n : ℕ} → T.TmExpr n → N.TmExpr Σ n
fTm (var x) = var x
fTm zero = sym (prev new) []
fTm (suc e) = sym new ([] , fTm e)


gTy : {n : ℕ} → N.TyExpr Σ n → T.TyExpr n
gTy (sym (prev (prev new)) []) = nat

gTm : {n : ℕ} → N.TmExpr Σ n → T.TmExpr n
gTm (var x) = var x
gTm (sym (prev (prev (prev ()))) x)
gTm (sym (prev new) []) = zero
gTm (sym new ([] , e)) = suc (gTm e)


{- Equalities -}

gfTy : {n : ℕ} (e : T.TyExpr n) → gTy (fTy e) ≡ e
gfTy nat = refl

gfTm : {n : ℕ} (e : T.TmExpr n) → gTm (fTm e) ≡ e
gfTm (var x) = refl
gfTm zero = refl
gfTm (suc e) = ap suc (gfTm e)


fgTy : {n : ℕ} (e : N.TyExpr Σ n) → fTy (gTy e) ≡ e
fgTy (sym (prev (prev new)) []) = refl

fgTm : {n : ℕ} (e : N.TmExpr Σ n) → fTm (gTm e) ≡ e
fgTm (var x) = refl
fgTm (sym (prev (prev (prev ()))) x)
fgTm (sym (prev new) []) = refl
fgTm (sym new ([] , e)) = ap (λ z → sym new ([] , z)) (fgTm e)


{- Derivability -}

data NJudgment : Set where
  njudgment : {n : ℕ} (Γ : N.Ctx Σ n) {k : JudgmentSort} → N.Judgment Σ Γ 0 k → NJudgment

NDerivable : NJudgment → Prop
NDerivable (njudgment Γ j) = N.Derivable E₃ j

fCtx : {n : ℕ} → T.Ctx n → N.Ctx Σ n
fCtx ◇ = ◇
fCtx (Γ , A) = (fCtx Γ , fTy A)

fJ : T.Judgment → NJudgment
fJ (Γ ⊢ A) = njudgment (fCtx Γ) (◇ ⊢ fTy A)
fJ (Γ ⊢ u :> A) = njudgment (fCtx Γ) (◇ ⊢ fTm u :> fTy A)
fJ (Γ ⊢ A == B) = njudgment (fCtx Γ) (◇ ⊢ fTy A == fTy B)
fJ (Γ ⊢ u == v :> A) = njudgment (fCtx Γ) (◇ ⊢ fTm u == fTm v :> fTy A)

fDer : {j : T.Judgment} → T.Derivable j → NDerivable (fJ j)
fDer (Var k d) = apply (prev (prev (prev {!var ?!}))) {!!}
fDer (TyRefl dA) = apply (prev (prev (prev tyRefl))) ([] , fDer dA)
fDer (TySymm dA=) = apply (prev (prev (prev tySymm))) ([] , {!!} , {!!} , fDer dA=)
fDer (TyTran d d₁ d₂) = {!!}
fDer (TmRefl d) = {!!}
fDer (TmSymm du=) = apply (prev (prev (prev tmSymm))) ([] , fDer du=)
fDer (TmTran d d₁ d₂) = {!!}
fDer (Conv dA du dA=) = apply (prev (prev (prev conv))) ([] , fDer du , fDer dA=)
fDer (ConvEq dA du= dA=) = apply (prev (prev (prev convEq))) ([] , fDer du= , fDer dA=)
fDer Nat = apply (prev (prev typingrule)) []
fDer NatCong = apply (prev (prev congruencerule)) []
fDer Zero = apply (prev typingrule) []
fDer ZeroCong = apply (prev congruencerule) []
fDer (Suc du) = apply typingrule ([] , fDer du)
fDer (SucCong du=) = apply congruencerule ([] , fDer du=)


gCtx : {n : ℕ} → N.Ctx Σ n → T.Ctx n
gCtx ◇ = ◇
gCtx (Γ , A) = (gCtx Γ , gTy A)

gJ : NJudgment → T.Judgment
gJ (njudgment Γ (◇ ⊢ A)) = gCtx Γ ⊢ gTy A
gJ (njudgment Γ (◇ ⊢ u :> A)) = gCtx Γ ⊢ gTm u :> gTy A
gJ (njudgment Γ (◇ ⊢ A == B)) = gCtx Γ ⊢ gTy A == gTy B
gJ (njudgment Γ (◇ ⊢ u == v :> A)) = gCtx Γ ⊢ gTm u == gTm v :> gTy A

gDer : {j : NJudgment} → NDerivable j → T.Derivable (gJ j)
gDer {njudgment Γ _} (apply typingrule {js = [] , (◇ ⊢ u :> .(sym (prev (prev new)) []))} ([] , du) {{tt , (refl , tt) , tt}}) = Suc (gDer du)
gDer {njudgment Γ _} (apply congruencerule {js = [] , (◇ ⊢ u == v :> .(sym (prev (prev new)) []))} ([] , du=) {{tt , (refl , (refl , tt)) , tt}}) = SucCong (gDer du=)
gDer {njudgment Γ _} (apply (prev typingrule) {js = []} []) = Zero
gDer {njudgment Γ _} (apply (prev congruencerule) {js = []} []) = ZeroCong
gDer {njudgment Γ _} (apply (prev (prev typingrule)) {js = []} []) = Nat
gDer {njudgment Γ _} (apply (prev (prev congruencerule)) {js = []} []) = NatCong
gDer {njudgment Γ _} (apply (prev (prev (prev (var k)))) {js = [] , (◇ ⊢ .(snd (N.get k Γ $ _)))} ([] , dA) {{getIsDef , (refl , tt)}}) = {!Var (fst (N.get k Γ $ getIsDef)) {!gDer dA!}!}
gDer {njudgment Γ _} (apply (prev (prev (prev conv))) {js = ([] , (◇ ⊢ u :> A)) , (◇ ⊢ .A == B)} ([] , du , dA=) {{refl , tt}}) = Conv {!!} (gDer du) (gDer dA=)
gDer {njudgment Γ _} (apply (prev (prev (prev convEq))) js-der) = {!!}
gDer {njudgment Γ _} (apply (prev (prev (prev tyRefl))) {js = [] , (◇ ⊢ A)} ([] , dA)) = TyRefl (gDer dA)
gDer {njudgment Γ _} (apply (prev (prev (prev tySymm))) js-der) = {!!}
gDer {njudgment Γ _} (apply (prev (prev (prev tyTran))) js-der) = {!!}
gDer {njudgment Γ _} (apply (prev (prev (prev tmRefl))) js-der) = {!!}
gDer {njudgment Γ _} (apply (prev (prev (prev tmSymm))) {js = [] , (◇ ⊢ u == v :> A)} ([] , du=)) = TmSymm (gDer du=)
gDer {njudgment Γ _} (apply (prev (prev (prev tmTran))) js-der) = {!!}
