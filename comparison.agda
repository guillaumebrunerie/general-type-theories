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

NDerivable=! : {j j' : NJudgment} (j= : j ≡ j') → NDerivable j → NDerivable j'
NDerivable=! refl x = x

T→NCtx : {n : ℕ} → T.Ctx n → N.Ctx Σ n
T→NCtx ◇ = ◇
T→NCtx (Γ , A) = (T→NCtx Γ , T→N A)

T→NJ : T.Judgment → NJudgment
T→NJ (Γ ⊢ A) = njudgment (T→NCtx Γ) (◇ ⊢ T→N A)
T→NJ (Γ ⊢ u :> A) = njudgment (T→NCtx Γ) (◇ ⊢ T→N u :> T→N A)
T→NJ (Γ ⊢ A == B) = njudgment (T→NCtx Γ) (◇ ⊢ T→N A == T→N B)
T→NJ (Γ ⊢ u == v :> A) = njudgment (T→NCtx Γ) (◇ ⊢ T→N u == T→N v :> T→N A)


weakenV-comm : {n : ℕ} (p : WeakPos n) (x : VarPos n) → N.weakenV p x ≡ T.weakenV p x
weakenV-comm last x = refl
weakenV-comm (prev p) last = refl
weakenV-comm (prev p) (prev x) = ap prev (weakenV-comm p x)

weaken-comm : {k : SyntaxSort} {n : ℕ} {A : T.Expr k n} (p : WeakPos n) → N.weaken p (T→N A) ≡ T→N (T.weaken p A)
weaken-comm {A = uu} p = refl
weaken-comm {A = el v} p = ap (λ z → sym new ([] , z)) (weaken-comm p)
weaken-comm {A = pi A B} p = ap2 (λ z z' → sym (prev (prev (prev (prev new)))) ([] , z , z')) (weaken-comm p) (weaken-comm (prev p))
weaken-comm {A = var x} p = ap var (weakenV-comm p x)
weaken-comm {A = lam A B u} p = ap3 (λ z z' z'' → sym (prev (prev (prev new))) ([] , z , z' , z'')) (weaken-comm p) (weaken-comm (prev p)) (weaken-comm (prev p))
weaken-comm {A = app A B f a} p = ap4 (λ z z' z'' z''' → sym (prev (prev new)) ([] , z , z' , z'' , z''')) (weaken-comm p) (weaken-comm (prev p)) (weaken-comm p) (weaken-comm p)


VarPos→ℕ : {n : ℕ} → VarPos n → ℕ
VarPos→ℕ last = 0
VarPos→ℕ (prev k) = suc (VarPos→ℕ k)

fst-VarPos→ℕ : {Σ : Signature} {n : ℕ} (k : VarPos n) (Γ : N.Ctx Σ n) {def : _} → fst (N.get (VarPos→ℕ k) Γ $ def) ≡ k
fst-VarPos→ℕ last (Γ , A) = refl
fst-VarPos→ℕ (prev k) (Γ , A) = ap prev (fst-VarPos→ℕ k Γ)

snd-VarPos→ℕ : {n : ℕ} (k : VarPos n) (Γ : T.Ctx n) {def : _} → snd (N.get (VarPos→ℕ k) (T→NCtx Γ) $ def) ≡ T→N (T.get k Γ)
snd-VarPos→ℕ last (Γ , A) = weaken-comm last
snd-VarPos→ℕ (prev k) (Γ , A) = ap (N.weaken last) (snd-VarPos→ℕ k Γ) ∙ weaken-comm last

get-def : {n : ℕ} (k : VarPos n) (Γ : T.Ctx n) → isDefined (N.get (VarPos→ℕ k) (T→NCtx Γ))
get-def last (Γ , A) = tt
get-def (prev k) (Γ , A) = (get-def k Γ , tt)


MorInsert : {Σ : Signature} (x : WeakPos m) (δ : N.Mor Σ n m) (u : N.TmExpr Σ n) → N.Mor Σ n (suc m)
MorInsert last δ u = (δ , u)
MorInsert (prev x) (δ , v) u = (MorInsert x δ u , v)

{-# REWRITE +O-rewrite #-}
{-# REWRITE +S-rewrite #-}
{-# REWRITE assoc #-}

weaken-MorInsert : {Σ : Signature} {n k : ℕ} {x : WeakPos n} {δ : N.Mor Σ k n} {u : N.TmExpr Σ k} → N.weakenMor (MorInsert x δ u) ≡ MorInsert x (N.weakenMor δ) (N.weaken last u)
weaken-MorInsert {x = last} = refl
weaken-MorInsert {x = prev x} {δ , u} = ap2 _,_ weaken-MorInsert refl

weakenVL-η : (y : VarPos n) {p : _} → y ≡ N.weakenVL {{p}} y
weakenVL-η y {≤r} = refl
weakenVL-η y {≤S p} = {!Impossible!}

weakenV-η : (x : WeakPos n) (y : VarPos n) {p : _} → y ≡ N.weakenV {{p}} x y
weakenV-η last y = weakenVL-η y
weakenV-η (prev x) last = refl
weakenV-η (prev x) (prev y) = ap prev (weakenV-η x y)

weaken-η  : {Σ : Signature} {k : _} {x : _} {p : _} {u : N.Expr Σ n k} → u ≡ N.weaken {{p}} x u
weakenA-η : {Σ : Signature} {k : _} {x : _} {p : _} {u : N.Args Σ n k} → u ≡ N.weakenA {{p}} x u

weaken-η {x = x} {u = var y} = ap var (weakenV-η x y)
weaken-η {u = sym s us} = ap (sym s) weakenA-η

weakenA-η {u = []} = refl
weakenA-η {u = u , x} = ap2 _,_ weakenA-η weaken-η


weaken-μ  : {Σ : Signature} {k : _} {x : _} {q : n ≤ m} {r : _} {u : N.Expr Σ n k} → N.weaken  {{≤S ≤r}} {!!} (N.weaken  {{q}} x u) ≡ N.weaken  {{r}} x u
weakenA-μ : {Σ : Signature} {k : _} {x : _} {q : n ≤ m} {r : _} {u : N.Args Σ n k} → N.weakenA {{≤S ≤r}} {!!} (N.weakenA {{q}} x u) ≡ N.weakenA {{r}} x u

weaken-μ {u = var x} = {!!}
weaken-μ {u = sym s x} = ap (sym s) weakenA-μ

weakenA-μ {u = []} = refl
weakenA-μ {u = u , x} = ap2 _,_ weakenA-μ {!weaken-μ!}



weaken+-MorInsert : {Σ : Signature} (m : ℕ) {n k : ℕ} {x : WeakPos n} {δ : N.Mor Σ k n} {u : N.TmExpr Σ k} {δ' : N.Mor Σ (k + m) (n + m)}
                  → N.weakenMor+ m δ ≡ δ' → N.weakenMor+ m (MorInsert x δ u) ≡ MorInsert (weakenWeakPos2 x) δ' (N.weaken last u)
weaken+-MorInsert zero refl = ap (MorInsert _ _) weaken-η
weaken+-MorInsert (suc m) refl = ap2 _,_ (ap N.weakenMor (weaken+-MorInsert m refl) ∙ weaken-MorInsert ∙ ap (MorInsert _ _) {!!}) refl

idMor+= : {Σ : Signature} (m : ℕ) → N.weakenMor+ {Σ} m {n = n} idMor ≡ idMor
idMor+= zero = refl
idMor+= (suc m) = ap2 _,_ (ap N.weakenMor (idMor+= m)) refl

SubstVL-insert : (y : VarPos (suc n)) → SubstMor {Σ = Σ} (var y) idMor ≡ var y
SubstVL-insert last = refl
SubstVL-insert (prev y) = {!!}

SubstV-insert : {n : ℕ} {y : VarPos (suc n)} {x : WeakPos (suc n)} {u : N.TmExpr Σ (suc n)} {p : _} → SubstMor (var (N.weakenV {{p}} x y)) (MorInsert x idMor u) ≡ var y
SubstV-insert {y = y} {x = last} {p = ≤S ≤r} = SubstVL-insert y
SubstV-insert {x = last} {p = ≤S (≤S p)} = {!impossible!}
SubstV-insert {y = last} {x = prev x} = refl
SubstV-insert {y = prev y} {x = prev x} = {!SubstV-insert!}

Subst-insert  : {k : SyntaxSort} {n : ℕ} {e : N.Expr Σ (suc n) k} {x : WeakPos (suc n)} {u : N.TmExpr Σ (suc n)} {p : _} → SubstMor (N.weaken {{p}} x e) (MorInsert x idMor u) ≡ e
SubstA-insert : {args : SyntaxArityArgs} {n : ℕ} {es : N.Args Σ (suc n) args} {x : WeakPos (suc n)} {u : N.TmExpr Σ (suc n)} {p : _} → SubstAMor (N.weakenA {{p}} x es) (MorInsert x idMor u) ≡ es

Subst-insert {e = var x} {x = x'} = SubstV-insert {x = x'}
Subst-insert {e = sym s x} = ap (sym s) SubstA-insert

SubstA-insert {es = []} = refl
SubstA-insert {args} {n} {es = _,_ {m = m} es e} {x = x} {u = u} {p = p} =
  ap2 _,_ SubstA-insert (ap (SubstMor (N.weaken {{≤+ m {suc n} {suc (suc n)} {{p}}}} (weakenWeakPos2 x) e)) (weaken+-MorInsert m (idMor+= m)) ∙ Subst-insert {e = e} {x = weakenWeakPos2 x})



T→NMor : T.Mor 0 n m → N.Mor Σ n m
T→NMor ◇ = ◇
T→NMor (δ , u) = (T→NMor δ , T→N u)

weakenMor-comm : {δ : T.Mor 0 n m} → N.weakenMor (T→NMor δ) ≡ T→NMor (T.weakenMor δ)
weakenMor-comm {δ = ◇} = refl
weakenMor-comm {δ = δ , u} = ap2 _,_ weakenMor-comm (weaken-comm last)

substV-lemma : (x : VarPos n) {δ : T.Mor 0 m n} → SubstMor (var x) (T→NMor δ) ≡ T→N (var x [ δ ])
substV-lemma last {δ , u} = refl
substV-lemma (prev x) {δ , u} = substV-lemma x


subst-lemma : {k : _} (B : T.Expr k n) {δ : T.Mor 0 m n} → SubstMor (T→N B) (T→NMor δ) ≡ T→N (B [ δ ])
subst-lemma uu = refl
subst-lemma (el v) = ap (λ z → sym new ([] , z)) (subst-lemma v)
subst-lemma (pi A B) = ap2 (λ z z' → sym (prev (prev (prev (prev new)))) ([] , z , z')) (subst-lemma A) (ap (SubstMor (T→N B)) (ap2 _,_ weakenMor-comm refl) ∙ subst-lemma B)
subst-lemma (var x) = substV-lemma x
subst-lemma (lam A B u) = ap3 (λ z z' z'' → sym (prev (prev (prev new))) ([] , z , z' , z''))
                            (subst-lemma A) (ap (SubstMor (T→N B)) (ap2 _,_ weakenMor-comm refl) ∙ subst-lemma B) (ap (SubstMor (T→N u)) (ap2 _,_ weakenMor-comm refl) ∙ subst-lemma u)
subst-lemma (app A B f a) = ap4
                              (λ z z' z'' z''' →
                                 sym (prev (prev new)) ([] , z , z' , z'' , z'''))
                              (subst-lemma A) (ap (SubstMor (T→N B)) (ap2 _,_ weakenMor-comm refl) ∙ subst-lemma B) (subst-lemma f) (subst-lemma a)



T→NDer : {j : T.Judgment} → T.Derivable j → NDerivable (T→NJ j)
T→NDer (Var {Γ = Γ} k dA) = NDerivable=! (ap (λ x → njudgment (T→NCtx Γ) (◇ ⊢ var x :> T→N (T.get k Γ))) (fst-VarPos→ℕ k (T→NCtx Γ))) (apr S (var (VarPos→ℕ k)) ([] ,0Ty T→NDer dA) {{get-def k Γ , (snd-VarPos→ℕ k Γ , tt)}})
T→NDer (TyRefl dA) = apr S tyRefl ([] , T→NDer dA)
T→NDer (TySymm dA=) = apr S tySymm ([] , T→NDer dA=)
T→NDer (TyTran dA= dB=) = apr S tyTran ([] , T→NDer dA= , T→NDer dB=)
T→NDer (TmRefl du) = apr S tmRefl ([] , T→NDer du)
T→NDer (TmSymm du=) = apr S tmSymm ([] , T→NDer du=)
T→NDer (TmTran du= dv=) = apr S tmTran ([] , T→NDer du= , T→NDer dv=)
T→NDer (Conv du dA=) = apr S conv ([] , T→NDer du , T→NDer dA=)
T→NDer (ConvEq du= dA=) = apr S convEq ([] , T→NDer du= , T→NDer dA=)
T→NDer UU = apr T 1 []
T→NDer UUCong = apr C 1 []
T→NDer (El dv) = apr T 0 ([] ,0Tm T→NDer dv)
T→NDer (ElCong dv=) = apr C 0 ([] ,0Tm= T→NDer dv=)
T→NDer (Pi dA dB) = apr T 4 ([] ,0Ty T→NDer dA ,1Ty T→NDer dB)
T→NDer (PiCong dA= dB=) = apr C 4 ([] ,0Ty= T→NDer dA= ,1Ty= T→NDer dB=)
T→NDer (Lam dA dB du) =
  NDerivable=! (ap (λ z → njudgment _ (◇ ⊢ sym (prev (prev (prev new))) ([] , T→N _ , T→N _ , T→N _) :> sym (prev (prev (prev (prev new)))) ([] , T→N _ , z))) p)
               (apr T 3 ([] ,0Ty T→NDer dA ,1Ty T→NDer dB ,1Tm NDerivable= (ap (λ z → njudgment _ (◇ ⊢ T→N _ :> z)) p) (T→NDer du)))  where

     p : {n : ℕ} {B : T.TyExpr (suc n)} → SubstMor (N.weaken {{≤-+ {m = 1}}} (prev last) (T→N B)) ((N.weakenMor idMor , var last) , var last) ≡ T→N B
     p = Subst-insert
T→NDer (LamCong dA= dB= du=) =
  NDerivable=! (ap (λ z → njudgment _ (◇ ⊢ sym (prev (prev (prev new))) ([] , T→N _ , T→N _ , T→N _) == sym (prev (prev (prev new))) ([] , T→N _ , T→N _ , T→N _) :> sym (prev (prev (prev (prev new)))) ([] , T→N _ , z)))
                   Subst-insert)
    (apr C 3 ([] ,0Ty= T→NDer dA= ,1Ty= T→NDer dB= ,1Tm= NDerivable= (ap (λ z → njudgment _ (◇ ⊢ T→N _ == T→N _ :> z)) Subst-insert) (T→NDer du=)))
T→NDer (App {A = A} {B} {f} {a} dA dB df da) =
  NDerivable=! (ap (λ z → njudgment _ (◇ ⊢ sym (prev (prev new)) ([] , T→N A , T→N B , T→N f , T→N a) :> z)) {!subst-lemma!})
    (apr T 2 ([] ,0Ty T→NDer dA
                 ,1Ty T→NDer dB
                 ,0Tm NDerivable= (ap (λ z → njudgment _ (◇ ⊢ T→N f :> sym (prev (prev (prev (prev new)))) ([] , T→N A , z))) Subst-insert) (T→NDer df)
                 ,0Tm T→NDer da))
T→NDer (AppCong {A = A} {A' = A'} {B = B} {B' = B'} {f = f} {f' = f'} {a = a} {a' = a'} dA= dB= df= da=) =
  NDerivable=! (ap (λ z → njudgment _ (◇ ⊢ sym (prev (prev new)) ([] , T→N A , T→N B , T→N f , T→N a) == sym (prev (prev new)) ([] , T→N A' , T→N B' , T→N f' , T→N a') :> z)) {!TODO!})
    (apr C 2 ([] ,0Ty= T→NDer dA=
                 ,1Ty= T→NDer dB=
                 ,0Tm= NDerivable= (ap (λ z → njudgment _ (◇ ⊢ T→N f == T→N f' :> sym (prev (prev (prev (prev new)))) ([] , T→N A , z))) Subst-insert)
                                   (T→NDer df=)
                 ,0Tm= T→NDer da=))
T→NDer (BetaPi {B = B} {u = u} dA dB du da) = NDerivable=! {!ap (λ z → njudgment _ (◇ ⊢ _ == _ !} (apr Eq 1 ([] ,0Ty T→NDer dA ,1Ty T→NDer dB ,1Tm NDerivable= (ap (λ z → njudgment _ (◇ ⊢ T→N u :> z)) Subst-insert) (T→NDer du) ,0Tm T→NDer da))


N→TCtx : {n : ℕ} → N.Ctx Σ n → T.Ctx n
N→TCtx ◇ = ◇
N→TCtx (Γ , A) = (N→TCtx Γ , N→T A)

weaken-comm' : {k : SyntaxSort} {n : ℕ} {A : N.Expr Σ n k} (p : WeakPos n) → N→T (N.weaken p A) ≡ T.weaken p (N→T A)
weaken-comm' p = ap N→T (ap (N.weaken p) (! (TNT _))) ∙ ap N→T (weaken-comm p) ∙ NTN _

get-eq : {n : ℕ} (k : ℕ) (Γ : N.Ctx Σ n) {def : _} → N→T (snd (N.get k Γ $ def)) ≡ T.get (fst (N.get k Γ $ def)) (N→TCtx Γ)
get-eq zero (Γ , A) = weaken-comm' last
get-eq (suc k) (Γ , A) = weaken-comm' last ∙ ap (T.weaken last) (get-eq k Γ)

N→TJ : NJudgment → T.Judgment
N→TJ (njudgment Γ (◇ ⊢ A)) = N→TCtx Γ ⊢ N→T A
N→TJ (njudgment Γ (◇ ⊢ u :> A)) = N→TCtx Γ ⊢ N→T u :> N→T A
N→TJ (njudgment Γ (◇ ⊢ A == B)) = N→TCtx Γ ⊢ N→T A == N→T B
N→TJ (njudgment Γ (◇ ⊢ u == v :> A)) = N→TCtx Γ ⊢ N→T u == N→T v :> N→T A

congTy : {Γ : T.Ctx n} {A A' : T.TyExpr n} → A ≡ A' → T.Derivable (Γ ⊢ A) → T.Derivable (Γ ⊢ A')
congTy refl d = d

congTmTy : {Γ : T.Ctx n} {u : T.TmExpr n} {A A' : T.TyExpr n} → A ≡ A' → T.Derivable (Γ ⊢ u :> A) → T.Derivable (Γ ⊢ u :> A')
congTmTy refl d = d

congTmTy! : {Γ : T.Ctx n} {u : T.TmExpr n} {A A' : T.TyExpr n} → A' ≡ A → T.Derivable (Γ ⊢ u :> A) → T.Derivable (Γ ⊢ u :> A')
congTmTy! refl d = d

congTmEqTy : {Γ : T.Ctx n} {u u' : T.TmExpr n} {A A' : T.TyExpr n} → A ≡ A' → T.Derivable (Γ ⊢ u == u' :> A) → T.Derivable (Γ ⊢ u == u' :> A')
congTmEqTy refl d = d

congTmEqTy! : {Γ : T.Ctx n} {u u' : T.TmExpr n} {A A' : T.TyExpr n} → A' ≡ A → T.Derivable (Γ ⊢ u == u' :> A) → T.Derivable (Γ ⊢ u == u' :> A')
congTmEqTy! refl d = d

N→TDer : {j : NJudgment} → NDerivable j → T.Derivable (N→TJ j)
-- N→TDer {njudgment Γ _} (apr Eq x js-der) = {!!}
N→TDer {njudgment Γ _} (apr S (var k) {js = [] , ◇ ⊢ A} ([] , dA) {{xᵈ , (refl , tt)}}) = congTmTy! (get-eq k Γ) (Var (fst (N.get k Γ $ xᵈ)) (congTy (get-eq k Γ) (N→TDer dA)))
N→TDer {njudgment Γ _} (apr S conv {js = [] , ◇ ⊢ u :> A , ◇ ⊢ A == B} ([] , du , dA=) {{refl , tt}}) = Conv (N→TDer du) (N→TDer dA=)
N→TDer {njudgment Γ _} (apr S convEq {js = [] , ◇ ⊢ u == v :> A , ◇ ⊢ A == B} ([] , du= , dA=) {{refl , tt}}) = ConvEq (N→TDer du=) (N→TDer dA=)
N→TDer {njudgment Γ _} (apr S tyRefl {js = [] , ◇ ⊢ A} ([] , dA)) = TyRefl (N→TDer dA)
N→TDer {njudgment Γ _} (apr S tySymm {js = [] , ◇ ⊢ A == B} ([] , dA=)) = TySymm (N→TDer dA=)
N→TDer {njudgment Γ _} (apr S tyTran {js = [] , ◇ ⊢ A == B , ◇ ⊢ B == D} ([] , dA= , dB=) {{refl , tt}}) = TyTran (N→TDer dA=) (N→TDer dB=)
N→TDer {njudgment Γ _} (apr S tmRefl {js = [] , ◇ ⊢ u :> A} ([] , du)) = TmRefl (N→TDer du)
N→TDer {njudgment Γ _} (apr S tmSymm {js = [] , ◇ ⊢ u == v :> A} ([] , du=)) = TmSymm (N→TDer du=)
N→TDer {njudgment Γ _} (apr S tmTran {js = [] , ◇ ⊢ u == v :> A , ◇ ⊢ v == w :> A} ([] , du= , dv=) {{refl , (refl , tt)}}) = TmTran (N→TDer du=) (N→TDer dv=)
N→TDer {njudgment Γ _} (apr T typingrule {js = [] , (◇ ⊢ v :> _)} ([] , dv) {{(tt , (tt , (refl , tt))) , tt }}) = El (N→TDer dv)
N→TDer {njudgment Γ _} (apr T (prev typingrule) []) = UU
--N→TDer {njudgment Γ _} (apr T (prev (prev typingrule)) {js = [] , ◇ ⊢ A , (◇ , _) ⊢ B , (◇ ⊢ f :> _) , (◇ ⊢ a :> _)} ([] , dA , dB , df , da)
--                            {{(((((tt , tt) , ((tt , refl) , tt)) , (tt , (refl , tt))) , (tt , (refl , tt))) , tt)}}) = {!N→TDer df --cong --App (N→TDer dA) (N→TDer dB) {!(N→TDer df)!} (N→TDer da)!}
-- N→TDer {njudgment Γ _} (apr T (prev (prev (prev typingrule))) {js = [] , ◇ ⊢ A , ((◇ , A) ⊢ B) , ((◇ , A) ⊢ u :> B)} ([] , dA , dB , du) {{(((tt , tt) , ((tt , refl) , tt)) , ((tt , refl) , (refl , tt)) ) , tt}})
--   = congTmTy! (ap (pi (N→T A)) (ap N→T Subst-insert)) (Lam (N→TDer dA) (N→TDer dB) (congTmTy (ap N→T Subst-insert) (N→TDer du)))
N→TDer {njudgment Γ _} (apr T (prev (prev (prev (prev typingrule)))) {js = [] , ◇ ⊢ A , (◇ , ._) ⊢ B} ([] , dA , dB) {{((tt , (tt , tt)) , ((tt , refl) , tt)) , tt}}) = Pi (N→TDer dA) (N→TDer dB)
N→TDer {njudgment Γ _} (apr C congruencerule {js = [] , ◇ ⊢ v == v' :> _} ([] , dv=) {{((tt , (tt , (refl , tt))) , tt)}}) = ElCong (N→TDer dv=)
N→TDer {njudgment Γ _} (apr C (prev congruencerule) []) = UUCong
N→TDer {njudgment Γ _} (apr C (prev (prev congruencerule)) js-der) = {!AppCong!}
--N→TDer {njudgment Γ _} (apr C (prev (prev (prev congruencerule))) {js = [] , ◇ ⊢ A == A' , ((◇ , A) ⊢ B == B') , ((◇ , A) ⊢ u == u' :> B'')} ([] , dA= , dB= , du=) {{(((tt , (tt , tt)) , ((tt , refl) , tt)) , ((tt , refl) , (refl , tt)) ) , tt}}) = congTmEqTy! (ap (pi (N→T A)) (ap N→T Subst-insert)) (LamCong (N→TDer dA=) (N→TDer dB=) (congTmEqTy (ap N→T Subst-insert) (N→TDer du=)))
N→TDer {njudgment Γ _} (apr C (prev (prev (prev (prev congruencerule)))) {js = [] , ◇ ⊢ A == A' , (◇ , ._) ⊢ B == B'} ([] , dA= , dB=) {{(((tt , (tt , tt)) , ((tt , refl) , tt)) , tt)}}) = PiCong (N→TDer dA=) (N→TDer dB=)
N→TDer {njudgment Γ _} (apr Eq equalityrule js-der) = {!Eta!}
N→TDer {njudgment Γ _} (apr Eq (prev equalityrule) js-der) = {!Beta!}
