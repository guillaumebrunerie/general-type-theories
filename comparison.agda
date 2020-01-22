{-# OPTIONS --rewriting --prop #-}

open import common

open import syntx as N
open import derivability as N
open import typingrules
open import structuralrules
open import typetheories
open import examples

open import traditional as T

Σ : Signature
Σ = TTSig ΠUEl-TT


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

NDerivable= : {j j' : NJudgment} (j= : j ≡ j') → NDerivable j' → NDerivable j
NDerivable= refl x = x

T→NCtx : {n : ℕ} → T.Ctx n → N.Ctx Σ n
T→NCtx ◇ = ◇
T→NCtx (Γ , A) = (T→NCtx Γ , T→N A)

T→NJ : T.Judgment → NJudgment
T→NJ (Γ ⊢ A) = njudgment (T→NCtx Γ) (◇ ⊢ T→N A)
T→NJ (Γ ⊢ u :> A) = njudgment (T→NCtx Γ) (◇ ⊢ T→N u :> T→N A)
T→NJ (Γ ⊢ A == B) = njudgment (T→NCtx Γ) (◇ ⊢ T→N A == T→N B)
T→NJ (Γ ⊢ u == v :> A) = njudgment (T→NCtx Γ) (◇ ⊢ T→N u == T→N v :> T→N A)

Subst1-weakenV : {Σ : Signature} {n : ℕ} {p : _} (x : VarPos (suc n)) {f : N.Expr Σ (suc n) Tm} → Subst1 0 (var (N.weakenVL {{p}} x)) f ≡ var x
Subst1-weakenV {p = ≤S ≤r} x = refl
Subst1-weakenV {p = ≤S (≤S p)} x = {!p absurd!}

Subst1-weaken : {Σ : Signature} {n : ℕ} {k : SyntaxSort} {p : _} (e : N.Expr Σ (suc n) k) {f : N.Expr Σ (suc n) Tm} → Subst1 0 (N.weaken {{p}} last e) f ≡ e
Subst1-weakenA : {Σ : Signature} {n : ℕ} {args : SyntaxArityArgs} {p : _} (es : N.Args Σ (suc n) args) {f : N.Expr Σ (suc n) Tm} → Subst1A 0 (N.weakenA {{p}} last es) f ≡ es

Subst1-weaken {p = p} (var x) {f = f} = Subst1-weakenV {p = p} x {f = f}
Subst1-weaken (sym s x) = ap (sym s) (Subst1-weakenA x)

Subst1-weakenA [] = refl
Subst1-weakenA (es , x) = ap2 _,_ (Subst1-weakenA es) {!!}

postulate
  Subst1-varlast' : {Σ : Signature} {n l : ℕ} (m : ℕ) {k : SyntaxSort} {p : _} (e : N.Expr Σ (suc (suc n) + m) k) → Subst1 m (N.weaken {{p}} last e) (var (last {l})) ≡ N.weaken {{{!!}}} last (Subst1 m e (var last))
--  Subst1-varlast' : {Σ : Signature} {n m : ℕ} {k : SyntaxSort} {p : _} (e : N.Expr Σ {!m!} k) → Subst1 0 (N.weaken {{p}} last e) (var (last {{!m!}})) ≡ e
-- Subst1-varlast zero (var x) = {!!}
-- Subst1-varlast (suc m) (var last) = {!!}
-- Subst1-varlast (suc m) (var (prev x)) = {!!}
-- Subst1-varlast zero (sym s x) = ap (sym s) {!!}
-- Subst1-varlast (suc m) (sym s x) = ap (sym s) {!!}


T→NDer : {j : T.Judgment} → T.Derivable j → NDerivable (T→NJ j)
T→NDer (Var k dA) = NDerivable= {!!} (apr S (var {!!}) ([] ,0Ty NDerivable= {!!} (T→NDer dA)))
T→NDer (TyRefl dA) = apr S tyRefl ([] , T→NDer dA)
T→NDer (TySymm dA=) = apr S tySymm ([] , T→NDer dA=)
T→NDer (TyTran dB dA= dB=) = apr S tyTran ([] , T→NDer dA= , T→NDer dB=)
T→NDer (TmRefl du) = apr S tmRefl ([] , T→NDer du)
T→NDer (TmSymm du=) = apr S tmSymm ([] , T→NDer du=)
T→NDer (TmTran dv du= dv=) = apr S tmTran ([] , T→NDer du= , T→NDer dv=)
T→NDer (Conv dA du dA=) = apr S conv ([] , T→NDer du , T→NDer dA=)
T→NDer (ConvEq dA du= dA=) = apr S convEq ([] , T→NDer du= , T→NDer dA=)
T→NDer UU = apr T 1 []
T→NDer UUCong = apr C 1 []
T→NDer (El dv) = apr T 0 ([] ,0Tm T→NDer dv)
T→NDer (ElCong dv=) = apr C 0 ([] ,0Tm= T→NDer dv=)
T→NDer (Pi dA dB) = apr T 4 ([] ,0Ty T→NDer dA ,1Ty NDerivable= (ap (λ z → njudgment (_ , z) (_ ⊢ _)) (weaken≤r _ ∙ weaken≤r _)) (T→NDer dB))
T→NDer (PiCong dA dA= dB=) = apr C 4 ([] ,0Ty= T→NDer dA= ,1Ty= NDerivable= (ap (λ z → njudgment (_ , z) (_ ⊢ _ == _)) (weaken≤r _ ∙ weaken≤r _)) (T→NDer dB=))
T→NDer (Lam {n = n} {A = A} {B = B} {u = u} dA dB du) = NDerivable= (! (ap (njudgment _) (ap3 (λ z z' z'' → ◇ ⊢ sym (prev (prev (prev new))) ([] , T→N A , z , T→N u) :> sym (prev (prev (prev (prev new)))) ([] , z' , z''))
                                                                                           (weaken≤r _)
                                                                                           (weaken≤r _ ∙ weaken≤r _)
                                                                                           q)))
                                            (apr T 3 (_,1Tm_ {u = T→N u} (_,1Ty_ {B = N.weaken {{≤r}} last (T→N B)} ([] ,0Ty T→NDer dA)
                                                            (NDerivable= (ap2 (λ z z' → njudgment (_ , z) (◇ ⊢ z')) (weaken≤r _ ∙ weaken≤r _) (weaken≤r _)) (T→NDer dB)))
                                                            (NDerivable= (ap3 (λ z z' z'' → njudgment (_ , z) (◇ ⊢ z' :> z'')) (weaken≤r _ ∙ weaken≤r _) refl p) (T→NDer du))))
                                                            where

     q = Subst1-weaken (N.weaken {{≤r}} (prev last) (N.weaken {{≤r}} last (T→N B))) {f = var last} ∙ weaken≤r _ ∙ weaken≤r _
     p = Subst1-varlast' 0 (N.weaken {{≤S ≤SS}} (prev last) (N.weaken {{≤r}} last (T→N B))) ∙ weaken≤r _ ∙ {!Subst1-varlast 0 (N.weaken last (T→N B))!} -- ∙ {!Subst1-last (weaken^' {n = {!!}} {1} {{!!}} {!!}) ∙ {!!}
                          -- ((apr T 3 ([] ,0Ty T→NDer dA
                          --               ,1Ty NDerivable= (ap2 (λ z z' → njudgment (_ , z) (◇ ⊢ z')) (! (weaken^'≤r _ ∙ weaken^'≤r _)) {!refl!}) (T→NDer dB)
                          --               ,1Tm NDerivable= (ap3 (λ z z' z'' → njudgment (_ , z) (◇ ⊢ z' :> z'')) (! (weaken^'≤r _ ∙ weaken^'≤r _)) {!!} (! (Subst1-last (T→N B)))) (T→NDer du))))
T→NDer (LamCong d d₁ d₂ d₃) = {!!}
T→NDer (App dA dB df da) = NDerivable= {!!} (apr T 2 ([] ,0Ty T→NDer dA
                                                         ,1Ty NDerivable= (ap (λ z → njudgment (T→NCtx _ , z) (◇ ⊢ _)) (weaken≤r _ ∙ weaken≤r _)) (T→NDer dB)
                                                         ,0Tm NDerivable= {!ap2 (λ z z' → njudgment (T→NCtx _) (◇ ⊢ T→N _ :> sym 4 ([] , z , z'))) (weaken≤r _ ∙ weaken≤r _) {!!}!} (T→NDer df)
                                                         ,0Tm NDerivable= (ap (λ z → njudgment (T→NCtx _) (◇ ⊢ T→N _ :> z)) (weaken≤r _ ∙ weaken≤r _)) (T→NDer da))) where

       q : Subst1 0 (N.weaken {{≤r}} last (N.weaken {{≤r}} (prev last) (T→N _))) (var last) ≡ T→N _
       q = Subst1-weaken (N.weaken (prev last) (T→N _)) {f = var last} ∙ weaken≤r _
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
N→TDer {njudgment Γ _} (apr S (var k) js-der) = {!Var!}
N→TDer {njudgment Γ _} (apr S conv js-der) = {!Conv!}
N→TDer {njudgment Γ _} (apr S convEq js-der) = {!ConvEq!}
N→TDer {njudgment Γ _} (apr S tyRefl {js = [] , ◇ ⊢ A} ([] , dA)) = TyRefl (N→TDer dA)
N→TDer {njudgment Γ _} (apr S tySymm {js = [] , ◇ ⊢ A == B} ([] , dA=)) = TySymm (N→TDer dA=)
N→TDer {njudgment Γ _} (apr S tyTran {js = [] , ◇ ⊢ A == B , ◇ ⊢ B == D} ([] , dA= , dB=) {{refl , tt}}) = TyTran {! -!} (N→TDer dA=) (N→TDer dB=)
N→TDer {njudgment Γ _} (apr S tmRefl {js = [] , ◇ ⊢ u :> A} ([] , du)) = TmRefl (N→TDer du)
N→TDer {njudgment Γ _} (apr S tmSymm {js = [] , ◇ ⊢ u == v :> A} ([] , du=)) = TmSymm (N→TDer du=)
N→TDer {njudgment Γ _} (apr S tmTran {js = [] , ◇ ⊢ u == v :> A , ◇ ⊢ v == w :> A} ([] , du= , dv=) {{refl , (refl , tt)}}) = TmTran {! -!} (N→TDer du=) (N→TDer dv=)
N→TDer {njudgment Γ _} (apr T typingrule {js = [] , (◇ ⊢ v :> _)} ([] , dv) {{(refl , tt) , tt }}) = El (N→TDer dv)
N→TDer {njudgment Γ _} (apr T (prev typingrule) []) = UU
N→TDer {njudgment Γ _} (apr T (prev (prev typingrule)) {js = [] , ◇ ⊢ A , (◇ , ._) ⊢ B , (◇ ⊢ f :> _) , (◇ ⊢ a :> _)} ([] , dA , dB , df , da)) = {!q !}
N→TDer {njudgment Γ _} (apr T (prev (prev (prev typingrule))) js-der) = {!Lam!}
N→TDer {njudgment Γ _} (apr T (prev (prev (prev (prev typingrule)))) {js = [] , ◇ ⊢ A , (◇ , ._) ⊢ B} ([] , dA , dB) {{(tt , ((refl , tt) , tt)) , tt}}) = Pi (N→TDer dA) {!N→TDer dB!}
N→TDer {njudgment Γ _} (apr C congruencerule {js = [] , ◇ ⊢ v == v' :> _} ([] , dv=) {{((refl , tt) , tt)}}) = ElCong (N→TDer dv=)
N→TDer {njudgment Γ _} (apr C (prev congruencerule) []) = UUCong
N→TDer {njudgment Γ _} (apr C (prev (prev congruencerule)) js-der) = {!AppCong!}
N→TDer {njudgment Γ _} (apr C (prev (prev (prev congruencerule))) js-der) = {!LamCong!}
N→TDer {njudgment Γ _} (apr C (prev (prev (prev (prev congruencerule)))) {js = [] , ◇ ⊢ A == A' , (◇ , ._) ⊢ B == B'} ([] , dA= , dB=) {{p}}) = PiCong {!!} (N→TDer dA=) {!p!}
N→TDer {njudgment Γ _} (apr Eq equalityrule js-der) = {!Eta!}
N→TDer {njudgment Γ _} (apr Eq (prev equalityrule) js-der) = {!Beta!}
