{-# OPTIONS --rewriting --prop #-}

open import common

open import syntx as N
open import derivability as N2
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
  njudgment : {n : ℕ} (Γ : N.Ctx Σ n) {k : JudgmentSort} → N2.Judgment Σ Γ 0 k → NJudgment

NDerivable : NJudgment → Prop
NDerivable (njudgment Γ j) = N2.Derivable (TTDer ΠUEl-TT) j

-- record NJudgment : Set where
--   constructor njudgment
--   field
--     {NJn} : ℕ
--     NJΓ : N.Ctx (TTSig ΠUEl-TT4)  NJn
--     {NJk} : JudgmentSort
--     NJj : N2.Judgment (TTSig ΠUEl-TT4) NJΓ 0 NJk

-- open NJudgment

-- record NDerivable (j : NJudgment) : Prop where
--   constructor ´_

--   field
--     `_ : N2.Derivable (TTDer ΠUEl-TT4) (NJj j)

-- open NDerivable

--   -- `_ : NDerivable (njudgment Γ j) → N2.Derivable (TTDer ΠUEl-TT) j
--   -- `_ d = d

--   -- ´_ : {n : ℕ} {Γ : N.Ctx Σ n} {k : JudgmentSort} {j : N2.Judgment Σ Γ 0 k} → N2.Derivable (TTDer ΠUEl-TT) j → NDerivable (njudgment Γ j)
--   -- ´_ d = d

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


weaken-comm : {k : SyntaxSort} {n : ℕ} {A : T.Expr k n} (p : WeakPos n) → N.weaken p (T→N A) ≡ T→N (T.weaken p A)
weaken-comm {A = uu} p = refl
weaken-comm {A = el v} p = ap (λ z → sym new ([] , z)) (weaken-comm p)
weaken-comm {A = pi A B} p = ap2 (λ z z' → sym (prev (prev (prev (prev new)))) ([] , z , z')) (weaken-comm p) (weaken-comm (prev p))
weaken-comm {A = var x} p = refl --ap var (weakenV-comm p x)
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

weaken-MorInsert : {Σ : Signature} {n k : ℕ} {x : WeakPos n} {δ : N.Mor Σ k n} {u : N.TmExpr Σ k}
                 → N.weakenMor (MorInsert x δ u) ≡ MorInsert x (N.weakenMor δ) (N.weaken last u)
weaken-MorInsert {x = last} = refl
weaken-MorInsert {x = prev x} {δ , u} = ap2 _,_ weaken-MorInsert refl

Impossible : {n k : ℕ} {A : Prop} → suc (n + k) ≤ n → A
Impossible {suc n} {k = zero} (≤S p) = Impossible p
Impossible {suc n} {k = suc k} p = Impossible (≤P p)

weakenV-η : (x : WeakPos n) (y : VarPos n) {p : n ≤ n} → y ≡ weakenV {{p}} x y
weakenV-η x y {≤r} = ! weakenV≤r
weakenV-η x y {≤S p} = Impossible p

weaken-η  : {Σ : Signature} {k : _} {x : _} {p : n ≤ n} {u : N.Expr Σ n k} → u ≡ N.weaken {{p}} x u
weakenA-η : {Σ : Signature} {k : _} {x : _} {p : n ≤ n} {u : N.Args Σ n k} → u ≡ N.weakenA {{p}} x u

weaken-η {x = x} {u = var y} = ap var (weakenV-η x y)
weaken-η {u = sym s us} = ap (sym s) weakenA-η

weakenA-η {u = []} = refl
weakenA-η {u = u , x} = ap2 _,_ weakenA-η weaken-η

WeakPosIncl : {n m : ℕ} {{_ : n ≤ m}} → WeakPos n → WeakPos m
WeakPosIncl last = last
WeakPosIncl {m = suc m} {{p}} (prev x) = prev (WeakPosIncl {{≤P p}} x)

≤P-≤SS : {n m : ℕ} (p : n ≤ m) → p ≡ ≤P (≤SS {{p}})
≤P-≤SS ≤r = refl
≤P-≤SS (≤S p) = ap ≤S (≤P-≤SS _)

WeakPosIncl-comm : {n m k : ℕ} {{p : n ≤ m}} {x : WeakPos n} → weakenPos (≤-+ {m = k}) (WeakPosIncl {{p}} x) ≡ WeakPosIncl {{≤+ k {{p}}}} (weakenPos ≤-+ x)
WeakPosIncl-comm {k = zero} {x = last} = refl
WeakPosIncl-comm {k = suc k} {x = last} = ap prev (WeakPosIncl-comm {k = k} {x = last} ∙ ap (λ z → WeakPosIncl {{z}} (weakenPos ≤-+ last)) (≤P-≤SS _))
WeakPosIncl-comm {m = suc m} {zero} {x = prev x} = refl
WeakPosIncl-comm {m = suc m} {suc k} {x = prev x} = ap prev (WeakPosIncl-comm {m = suc m} {k = k} {x = prev x} ∙ ap (λ z → WeakPosIncl {{z}} (weakenPos ≤-+ (prev x))) (≤P-≤SS _))

≤-ishProp : {n m : ℕ} (p q : n ≤ m) → p ≡ q
≤-ishProp ≤r ≤r = refl
≤-ishProp ≤r (≤S q) = Impossible q
≤-ishProp (≤S p) ≤r = Impossible p
≤-ishProp (≤S p) (≤S q) = ap ≤S (≤-ishProp p q)

weakenV-μ : {n m k : ℕ} {{p : n ≤ m}} {{q : m ≤ k}} {{r : n ≤ k}} {x : VarPos n} {y : WeakPos n}
            → weakenV {{q}} (WeakPosIncl y) (weakenV {{p}} y x) ≡ weakenV {{r}} y x
weakenV-μ ⦃ p = ≤r ⦄ ⦃ ≤r ⦄ ⦃ ≤r ⦄ = weakenV≤r
weakenV-μ ⦃ p = ≤r ⦄ ⦃ ≤r ⦄ ⦃ ≤S r ⦄ = Impossible r
weakenV-μ ⦃ p = ≤r ⦄ ⦃ ≤S q ⦄ ⦃ ≤r ⦄ = Impossible q
weakenV-μ ⦃ p = ≤r ⦄ ⦃ ≤S q ⦄ ⦃ ≤S r ⦄ {x} {y = last} = ap2 (λ z z' → prev (weakenV ⦃ z ⦄ last z')) (≤-ishProp _ _) weakenV≤r
weakenV-μ ⦃ p = ≤r ⦄ ⦃ ≤S q ⦄ ⦃ ≤S r ⦄ {last} {y = prev y} = refl
weakenV-μ ⦃ p = ≤r ⦄ ⦃ ≤S q ⦄ ⦃ ≤S r ⦄ {prev x} {y = prev y} = ap prev (ap (weakenV {{≤P (≤S q)}} (WeakPosIncl y)) (! weakenV≤r) ∙ weakenV-μ {{≤r}} {{≤P (≤S q)}} {{≤P (≤S r)}} {x = x} {y})
weakenV-μ ⦃ p = ≤S p ⦄ ⦃ ≤r ⦄ ⦃ ≤r ⦄ = Impossible p
weakenV-μ ⦃ p = ≤S p ⦄ ⦃ ≤r ⦄ ⦃ ≤S r ⦄ {x} {y} = weakenV≤r {p = WeakPosIncl {{≤S p}} y} {v = weakenV {{≤S p}} y x} ∙ ap (λ z → weakenV ⦃ z ⦄ y x) (≤-ishProp _ _) --
weakenV-μ ⦃ p = ≤S p ⦄ ⦃ ≤S q ⦄ ⦃ ≤r ⦄ = Impossible (≤tr {{≤S p}} {{q}})
weakenV-μ ⦃ p = ≤S p ⦄ ⦃ ≤S q ⦄ ⦃ ≤S ≤r ⦄ = Impossible (≤tr {{q}} {{p}})
weakenV-μ ⦃ p = ≤S p ⦄ ⦃ ≤S q ⦄ ⦃ ≤S (≤S r) ⦄ {x} {y = last} = ap prev (weakenV-μ {{≤S p}} {{q}} {{≤S r}} {x} {last})
weakenV-μ ⦃ p = ≤S p ⦄ ⦃ ≤S q ⦄ ⦃ ≤S (≤S r) ⦄ {last} {y = prev y} = refl
weakenV-μ ⦃ p = ≤S p ⦄ ⦃ ≤S q ⦄ ⦃ ≤S (≤S r) ⦄ {prev x} {y = prev y} = ap prev (weakenV-μ {{≤P (≤S p)}} {{≤P (≤S q)}} {{≤P (≤S (≤S r))}} {x} {y})

weaken-μ  : {Σ : Signature} {k : _} {x : WeakPos n} {q : n ≤ m} {r : _} {u : N.Expr Σ n k} → N.weaken  {{≤S ≤r}} (WeakPosIncl {{q}} x) (N.weaken  {{q}} x u) ≡ N.weaken  {{r}} x u
weakenA-μ : {Σ : Signature} {k : _} {x : WeakPos n} {q : n ≤ m} {r : _} {u : N.Args Σ n k} → N.weakenA {{≤S ≤r}} (WeakPosIncl {{q}} x) (N.weakenA {{q}} x u) ≡ N.weakenA {{r}} x u

weaken-μ {x = y} {q = p} {u = var x} = ap var ((weakenV-μ {{p}} {{≤S ≤r}} {{_}} {x = x} {y = y}))
weaken-μ {u = sym s x} = ap (sym s) weakenA-μ

weakenA-μ {u = []} = refl
weakenA-μ {q = q} {u = u , x} = ap2 _,_ weakenA-μ (ap2 (λ z z' → N.weaken {{z}} z' (N.weaken {{≤+ _ {{q}}}} _ x))
                                                       (≤-ishProp _ _)
                                                       (WeakPosIncl-comm {{q}})
                                                   ∙ weaken-μ {q = ≤+ _ {{q}}})



weaken+-MorInsert : {Σ : Signature} (m : ℕ) {n k : ℕ} {x : WeakPos n} {δ : N.Mor Σ k n} {u : N.TmExpr Σ k}
                    → N.weakenMor+ m (MorInsert x δ u) ≡ MorInsert (weakenPos ≤-+ x) (N.weakenMor+ m δ) (N.weaken last u)
weaken+-MorInsert zero = ap (MorInsert _ _) weaken-η
weaken+-MorInsert (suc m) = ap2 _,_ (ap N.weakenMor (weaken+-MorInsert m) ∙ weaken-MorInsert ∙ ap (MorInsert _ _) weaken-μ) refl

SubstV-insert : {n m : ℕ} {y : VarPos n} {x : WeakPos n} {u : N.TmExpr Σ m} {δ : N.Mor Σ m n} {p : n ≤ suc n}
                → SubstMor (var (weakenV {{p}} x y)) (MorInsert x δ u) ≡ SubstMor (var y) δ
SubstV-insert {x = last} {δ = δ} {p = ≤S ≤r} = ap (λ z → SubstMor (var z) δ) weakenV≤r
SubstV-insert {y = last} {x = prev x} {δ = δ , v} {p = ≤S ≤r} = refl
SubstV-insert {y = prev y} {x = prev x} {u} {δ = δ , v} {p = ≤S ≤r} = SubstV-insert {y = y} {x = x} {u = u} {δ = δ} {p = ≤S ≤r}
SubstV-insert {p = ≤S (≤S p)} = Impossible p

Subst-insert  : {k : SyntaxSort} {n m : ℕ} {e : N.Expr Σ n k} {x : WeakPos n} {u : N.TmExpr Σ m} {δ : N.Mor Σ m n} {p : _}
                → SubstMor (N.weaken {{p}} x e) (MorInsert x δ u) ≡ SubstMor e δ
SubstA-insert : {args : SyntaxArityArgs} {n m : ℕ} {es : N.Args Σ n args} {x : WeakPos n} {u : N.TmExpr Σ m} {δ : N.Mor Σ m n} {p : _}
                → SubstAMor (N.weakenA {{p}} x es) (MorInsert x δ u) ≡ SubstAMor es δ

Subst-insert {e = var x} {x = x'} {u} {p = p} = SubstV-insert {x = x'} {u} {p = p}
Subst-insert {e = sym s x} = ap (sym s) SubstA-insert

SubstA-insert {es = []} = refl
SubstA-insert {args} {n} {es = _,_ {m = m} es e} {x = x} {u = u} {p = p} =
  ap2 _,_ SubstA-insert (ap (SubstMor (N.weaken {{≤+ m {n} {suc n} {{p}}}} (weakenPos ≤-+ x) e)) (weaken+-MorInsert m) ∙ Subst-insert {e = e} {x = weakenPos ≤-+ x})


weakenMor+-idMor : {n : ℕ} (m : ℕ) → N.weakenMor+ m (N.idMor {Σ = Σ} {n = n}) ≡ N.idMor
weakenMor+-idMor zero = refl
weakenMor+-idMor (suc m) = ap2 _,_ (ap N.weakenMor (weakenMor+-idMor m)) refl

SubstMor-weakenMor : {x : VarPos n} {δ : N.Mor Σ m n} → SubstMor (var x) (N.weakenMor δ) ≡ N.weaken last (SubstMor (var x) δ)
SubstMor-weakenMor {x = last} {δ , u} = refl
SubstMor-weakenMor {x = prev x} {δ , u} = SubstMor-weakenMor {x = x} {δ}

SubstMor-idMor  : {n : ℕ} {k : _} (e  : N.Expr Σ n k) → SubstMor e N.idMor ≡ e
SubstAMor-idMor : {n : ℕ} {k : _} (es : N.Args Σ n k) → SubstAMor es N.idMor ≡ es

SubstMor-idMor (var last) = refl
SubstMor-idMor (var (prev x)) = SubstMor-weakenMor {x = x} {δ = N.idMor} ∙ ap (N.weaken last) (SubstMor-idMor (var x)) ∙ ap var (ap prev weakenV≤r)
SubstMor-idMor (sym s es) = ap (sym s) (SubstAMor-idMor es)

SubstAMor-idMor [] = refl
SubstAMor-idMor (_,_ {m = m} es x) = ap2 _,_ (SubstAMor-idMor es) (ap (SubstMor x) (weakenMor+-idMor m) ∙ SubstMor-idMor x)


Subst-insert-idMor : {k : SyntaxSort} {e : N.Expr Σ n k} {x : WeakPos n} {u : N.TmExpr Σ n} {p : _}
                    → SubstMor (N.weaken {{p}} x e) (MorInsert x N.idMor u) ≡ e
Subst-insert-idMor {e = e} {x} {u} {p} = Subst-insert {e = e} {x} {u} {N.idMor} {p} ∙ SubstMor-idMor e

inj : WeakPos n → WeakPos (suc n)
inj last = last
inj (prev x) = prev (inj x)

weakenPos-inj : {m : ℕ} (x : WeakPos n) → weakenPos (≤-+ {m = m}) (inj x) ≡ inj (weakenPos ≤-+ x)
weakenPos-inj {m = zero} x = refl
weakenPos-inj {m = suc m} last = ap prev (weakenPos-inj last)
weakenPos-inj {m = suc m} (prev x) = ap prev (weakenPos-inj (prev x))

SubstV-insert2 : {n m : ℕ} {y : VarPos n} {x : WeakPos n} {u : N.TmExpr Σ (suc m)} {δ : N.Mor Σ (suc m) (suc n)} {p : _}
                → SubstMor (var (weakenV {{≤S p}} x y)) (MorInsert (inj x) δ u) ≡ SubstMor (var (weakenV {{p}} x y)) δ
SubstV-insert2 {y = last} {last} = refl
SubstV-insert2 {y = prev y} {last} = refl
SubstV-insert2 {y = last} {prev x} {δ = δ , u} = refl
SubstV-insert2 {y = prev y} {prev x} {δ = δ , u} {≤S ≤r} = SubstV-insert2 {y = y} {x = x} {δ = δ}
SubstV-insert2 {y = prev y} {prev x} {δ = δ , u} {≤S (≤S p)} = Impossible p

Subst-insert2  : {k : SyntaxSort} {n m : ℕ} {e : N.Expr Σ n k} {x : WeakPos n} {u : N.TmExpr Σ (suc m)} {δ : N.Mor Σ (suc m) (suc n)} {p : _}
                 → SubstMor (N.weaken {{≤S p}} x e) (MorInsert (inj x) δ u) ≡ SubstMor (N.weaken {{p}} x e) δ
SubstA-insert2  : {args : SyntaxArityArgs} {n m : ℕ} {es : N.Args Σ n args} {x : WeakPos n} {u : N.TmExpr Σ (suc m)} {δ : N.Mor Σ (suc m) (suc n)} {p : _}
                 → SubstAMor (N.weakenA {{≤S p}} x es) (MorInsert (inj x) δ u) ≡ SubstAMor (N.weakenA {{p}} x es) δ

Subst-insert2 {e = var y} {x = x} = SubstV-insert2 {y = y} {x = x}
Subst-insert2 {e = sym s es} = ap (sym s) SubstA-insert2

SubstA-insert2 {es = []} = refl
SubstA-insert2 {n = n} {m = m'} {es = _,_ {m = m} es e} {x = x} {u = u} =
  ap2 _,_ SubstA-insert2 ((ap (SubstMor (N.weaken {{_}} (weakenPos ≤-+ x) e)) (weaken+-MorInsert m ∙ ap3 MorInsert (weakenPos-inj x) refl refl)
                          ∙ ap
                              (λ z →
                                 SubstMor (N.weaken ⦃ z ⦄ (weakenPos ≤-+ x) e)
                                 (MorInsert (inj (weakenPos ≤-+ x)) (N.weakenMor+ m {n = suc n} {m = suc m'} _)
                                  (N.weaken last u)))
                              (≤-ishProp _ _) ∙ Subst-insert2 {e = e} {x = weakenPos ≤-+ x} {u = N.weaken last u}))

Subst-insert-idMor2 : {k : SyntaxSort} {e : N.Expr Σ n k} {x : WeakPos n} {u : N.TmExpr Σ (suc n)}
                    → SubstMor (N.weaken x e) (MorInsert (inj x) (N.idMor {n = suc n}) u) ≡ N.weaken {{≤S ≤r}} x e
Subst-insert-idMor2 {e = e} {x} {u} = Subst-insert2 {e = e} {x} {u} {N.idMor} ∙ SubstMor-idMor _

T→NMor : T.Mor n m → N.Mor Σ n m
T→NMor ◇ = ◇
T→NMor (δ , u) = (T→NMor δ , T→N u)

weakenMor-comm : {δ : T.Mor n m} → N.weakenMor (T→NMor δ) ≡ T→NMor (T.weakenMor δ)
weakenMor-comm {δ = ◇} = refl
weakenMor-comm {δ = δ , u} = ap2 _,_ weakenMor-comm (weaken-comm last)

substV-lemma : (x : VarPos n) {δ : T.Mor m n} → SubstMor (var x) (T→NMor δ) ≡ T→N (var x [ δ ])
substV-lemma last {δ , u} = refl
substV-lemma (prev x) {δ , u} = substV-lemma x


subst-lemma : {k : _} (B : T.Expr k n) {δ : T.Mor m n} → SubstMor (T→N B) (T→NMor δ) ≡ T→N (B [ δ ])
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

idMor-lemma : {n : ℕ} → N.idMor {n = n} ≡ T→NMor T.idMor
idMor-lemma {zero} = refl
idMor-lemma {suc n} = ap2 _,_ (ap N.weakenMor idMor-lemma ∙ weakenMor-comm) refl

Subst-T→N : {k : _} (B : T.Expr k (suc n)) (a : T.TmExpr n) → N.SubstMor (T→N B) (N.idMor , T→N a) ≡ T→N (T.subst B a)
Subst-T→N B a = ap (λ z → SubstMor (T→N B) (z , T→N a)) idMor-lemma ∙ subst-lemma B

-- T→NDer : {j : T.Judgment} → T.Derivable j → NDerivable (T→NJ j)
-- T→NDer (Var {Γ = Γ} k dA) = NDerivable=! (ap (λ x → njudgment (T→NCtx Γ) (◇ ⊢ var x :> T→N (T.get k Γ))) (fst-VarPos→ℕ k (T→NCtx Γ))) (´ apr S (var (VarPos→ℕ k)) ([] ,0Ty ` T→NDer dA) {{get-def k Γ , (snd-VarPos→ℕ k Γ , tt)}})
-- T→NDer (TyRefl dA) = ´ apr S tyRefl ([] , ` T→NDer dA)
-- T→NDer (TySymm dA=) = ´ apr S tySymm ([] , ` T→NDer dA=)
-- T→NDer (TyTran dA= dB=) = ´ apr S tyTran ([] , ` T→NDer dA= , ` T→NDer dB=)
-- T→NDer (TmRefl du) = ´ apr S tmRefl ([] , ` T→NDer du)
-- T→NDer (TmSymm du=) = ´ apr S tmSymm ([] , ` T→NDer du=)
-- -- T→NDer (TmTran du= dv=) = apr S tmTran ([] , T→NDer du= , T→NDer dv=)
-- -- T→NDer (Conv du dA=) = apr S conv ([] , T→NDer du , T→NDer dA=)
-- -- T→NDer (ConvEq du= dA=) = apr S convEq ([] , T→NDer du= , T→NDer dA=)
-- -- T→NDer UU = apr T 1 []
-- -- T→NDer UUCong = apr C 1 []
-- -- T→NDer (El dv) = apr T 0 ([] ,0Tm T→NDer dv)
-- -- T→NDer (ElCong dv=) = apr C 0 ([] ,0Tm= T→NDer dv=)
-- -- T→NDer (Pi dA dB) = apr T 4 ([] ,0Ty T→NDer dA ,1Ty T→NDer dB)
-- -- T→NDer (PiCong dA= dB=) = apr C 4 ([] ,0Ty= T→NDer dA= ,1Ty= T→NDer dB=)
-- -- T→NDer (Lam {A = A} {B = B} {u = u} dA dB du) =
-- --   NDerivable=! (ap (λ z → njudgment _ (◇ ⊢ sym (prev (prev (prev new))) ([] , T→N _ , T→N _ , T→N _) :> sym (prev (prev (prev (prev new)))) ([] , T→N _ , z))) Subst-insert-idMor)
-- --                (apr T 3 ([] ,0Ty T→NDer dA ,1Ty T→NDer dB ,1Tm NDerivable= (ap (λ z → njudgment _ (◇ ⊢ T→N _ :> z)) Subst-insert-idMor) (T→NDer du)))
-- -- T→NDer (LamCong dA= dB= du=) =
-- --   NDerivable=! (ap (λ z → njudgment _ (◇ ⊢ sym (prev (prev (prev new))) ([] , T→N _ , T→N _ , T→N _) == sym (prev (prev (prev new))) ([] , T→N _ , T→N _ , T→N _) :> sym (prev (prev (prev (prev new)))) ([] , T→N _ , z)))
-- --                    Subst-insert-idMor)
-- --     (apr C 3 ([] ,0Ty= T→NDer dA= ,1Ty= T→NDer dB= ,1Tm= NDerivable= (ap (λ z → njudgment _ (◇ ⊢ T→N _ == T→N _ :> z)) Subst-insert-idMor) (T→NDer du=)))
-- -- T→NDer (App {A = A} {B} {f} {a} dA dB df da) =
-- --   NDerivable=! (ap (λ z → njudgment _ (◇ ⊢ sym (prev (prev new)) ([] , T→N A , T→N B , T→N f , T→N a) :> z)) (Subst-T→N B a))
-- --     (apr T 2 ([] ,0Ty T→NDer dA
-- --                  ,1Ty T→NDer dB
-- --                  ,0Tm NDerivable= (ap (λ z → njudgment _ (◇ ⊢ T→N f :> sym (prev (prev (prev (prev new)))) ([] , T→N A , z))) Subst-insert-idMor) (T→NDer df)
-- --                  ,0Tm T→NDer da))
-- -- T→NDer (AppCong {A = A} {A' = A'} {B = B} {B' = B'} {f = f} {f' = f'} {a = a} {a' = a'} dA= dB= df= da=) =
-- --   NDerivable=! (ap (λ z → njudgment _ (◇ ⊢ sym (prev (prev new)) ([] , T→N A , T→N B , T→N f , T→N a) == sym (prev (prev new)) ([] , T→N A' , T→N B' , T→N f' , T→N a') :> z)) (Subst-T→N B a))
-- --     (apr C 2 ([] ,0Ty= T→NDer dA=
-- --                  ,1Ty= T→NDer dB=
-- --                  ,0Tm= NDerivable= (ap (λ z → njudgment _ (◇ ⊢ T→N f == T→N f' :> sym (prev (prev (prev (prev new)))) ([] , T→N A , z))) Subst-insert-idMor)
-- --                                    (T→NDer df=)
-- --                  ,0Tm= T→NDer da=))
-- -- T→NDer (BetaPi {A = A} {B = B} {u = u} {a = a} dA dB du da) =
-- --   NDerivable=! (ap4
-- --                   (λ z z' z'' z''' →
-- --                      njudgment _
-- --                      (◇ ⊢
-- --                       sym (prev (prev new))
-- --                       ([] , T→N A , z ,
-- --                        sym (prev (prev (prev new))) ([] , T→N A , z , z')
-- --                        , T→N a)
-- --                       == z'' :> z'''))
-- --                   Subst-insert-idMor Subst-insert-idMor (Subst-T→N u a) (Subst-T→N B a))
-- --                (apr Eq 1 ([] ,0Ty T→NDer dA ,1Ty T→NDer dB ,1Tm NDerivable= (ap (λ z → njudgment _ (◇ ⊢ T→N u :> z)) Subst-insert-idMor) (T→NDer du) ,0Tm T→NDer da))
-- -- T→NDer (EtaPi {n = n} {A = A} {B = B} {f = f} dA dB df) =
-- --   NDerivable=! (ap4
-- --                   (λ z z' z'' z''' →
-- --                      njudgment _
-- --                      (◇ ⊢ T→N f ==
-- --                       sym (prev (prev (prev new)))
-- --                       ([] , T→N A , z ,
-- --                        sym (prev (prev new)) ([] , z' , z'' , z''' , var last))
-- --                       :> sym (prev (prev (prev (prev new)))) ([] , T→N A , z)))
-- --                   Subst-insert-idMor (weaken-comm last) (Subst-insert-idMor2 ∙ weaken-comm (prev last)) (weaken-comm last))
-- --                (apr Eq 0 ([] ,0Ty T→NDer dA
-- --                              ,1Ty T→NDer dB
-- --                              ,0Tm NDerivable= (ap (λ z → njudgment _ (◇ ⊢ T→N f :> sym (prev (prev (prev (prev new)))) ([] , T→N A , z))) Subst-insert-idMor) (T→NDer df)))


N→TCtx : {n : ℕ} → N.Ctx Σ n → T.Ctx n
N→TCtx ◇ = ◇
N→TCtx (Γ , A) = (N→TCtx Γ , N→T A)

N→TMor : {n m : ℕ} → N.Mor Σ n m → T.Mor n m
N→TMor ◇ = ◇
N→TMor (δ , u) = (N→TMor δ , N→T u)

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

congTmEq : {Γ : T.Ctx n} {u u' v v' : T.TmExpr n} {A A' : T.TyExpr n} → A ≡ A' → u ≡ u' → v ≡ v' → T.Derivable (Γ ⊢ u == v :> A) → T.Derivable (Γ ⊢ u' == v' :> A')
congTmEq refl refl refl d = d

congTmEq! : {Γ : T.Ctx n} {u u' v v' : T.TmExpr n} {A A' : T.TyExpr n} → A' ≡ A → u' ≡ u → v' ≡ v → T.Derivable (Γ ⊢ u == v :> A) → T.Derivable (Γ ⊢ u' == v' :> A')
congTmEq! refl refl refl d = d

N→T-Subst : {k : _} (B : N.Expr Σ (suc n) k) (a : N.TmExpr Σ n) → N→T (SubstMor B (N.idMor , a)) ≡ T.subst (N→T B) (N→T a)
N→T-Subst B a = ap N→T (! (ap2 SubstMor (TNT B) (ap2 _,_ refl (TNT a))) ∙ Subst-T→N (N→T B) (N→T a)) ∙ NTN _

N→TDer : {j : NJudgment} → NDerivable j → T.Derivable (N→TJ j)

-- N→TDer {njudgment Γ _} (apr S (var k) {js = [] , ◇ ⊢ A} ([] , dA) {{xᵈ , (refl , tt)}}) = congTmTy! (get-eq k Γ) (Var (fst (N.get k Γ $ xᵈ)) (congTy (get-eq k Γ) (N→TDer dA)))
-- N→TDer {njudgment Γ _} (apr S conv {js = [] , ◇ ⊢ u :> A , ◇ ⊢ A == B} ([] , du , dA=) {{refl , tt}}) = Conv (N→TDer du) (N→TDer dA=)
-- N→TDer {njudgment Γ _} (apr S convEq {js = [] , ◇ ⊢ u == v :> A , ◇ ⊢ A == B} ([] , du= , dA=) {{refl , tt}}) = ConvEq (N→TDer du=) (N→TDer dA=)
-- N→TDer {njudgment Γ _} (apr S tyRefl {js = [] , ◇ ⊢ A} ([] , dA)) = TyRefl (N→TDer dA)
-- N→TDer {njudgment Γ _} (apr S tySymm {js = [] , ◇ ⊢ A == B} ([] , dA=)) = TySymm (N→TDer dA=)
-- N→TDer {njudgment Γ _} (apr S tyTran {js = [] , ◇ ⊢ A == B , ◇ ⊢ B == D} ([] , dA= , dB=) {{refl , tt}}) = TyTran (N→TDer dA=) (N→TDer dB=)
-- N→TDer {njudgment Γ _} (apr S tmRefl {js = [] , ◇ ⊢ u :> A} ([] , du)) = TmRefl (N→TDer du)
-- N→TDer {njudgment Γ _} (apr S tmSymm {js = [] , ◇ ⊢ u == v :> A} ([] , du=)) = TmSymm (N→TDer du=)
-- N→TDer {njudgment Γ _} (apr S tmTran {js = [] , ◇ ⊢ u == v :> A , ◇ ⊢ v == w :> A} ([] , du= , dv=) {{refl , (refl , tt)}}) = TmTran (N→TDer du=) (N→TDer dv=)
-- N→TDer {njudgment Γ _} (apr T typingrule {js = [] , (◇ ⊢ v :> _)} ([] , dv) {{(tt , (tt , (refl , tt))) , tt}}) = El (N→TDer dv)
-- N→TDer {njudgment Γ _} (apr T (prev typingrule) []) = UU
-- N→TDer {njudgment Γ _} (apr T (prev (prev typingrule)) {js = [] , ◇ ⊢ A , (◇ , _) ⊢ B , (◇ ⊢ f :> _) , (◇ ⊢ a :> _)} ([] , dA , dB , df , da)
--                            {{(((((tt , (tt , tt)) , ((tt , refl) , tt)) , (tt , (refl , tt))) , (tt , (refl , tt))) , tt)}}) = congTmTy! (N→T-Subst B a) (App (N→TDer dA) (N→TDer dB) (congTmTy (ap (pi (N→T A)) (ap N→T Subst-insert-idMor)) (N→TDer df)) (N→TDer da))
-- N→TDer {njudgment Γ _} (apr T (prev (prev (prev typingrule))) {js = [] , ◇ ⊢ A , ((◇ , A) ⊢ B) , ((◇ , A) ⊢ u :> B')} ([] , dA , dB , du) {{(((tt , (tt , tt)) , ((tt , refl) , tt)) , ((tt , refl) , (refl , tt)) ) , tt}})
--   = congTmTy! (ap (pi (N→T A)) (ap N→T Subst-insert-idMor)) (Lam (N→TDer dA) (N→TDer dB) (congTmTy (ap N→T Subst-insert-idMor) (N→TDer du)))
-- N→TDer {njudgment Γ _} (apr T (prev (prev (prev (prev typingrule)))) {js = [] , ◇ ⊢ A , (◇ , ._) ⊢ B} ([] , dA , dB) {{((tt , (tt , tt)) , ((tt , refl) , tt)) , tt}}) = Pi (N→TDer dA) (N→TDer dB)
-- N→TDer {njudgment Γ _} (apr C congruencerule {js = [] , ◇ ⊢ v == v' :> _} ([] , dv=) {{((tt , (tt , (refl , tt))) , tt)}}) = ElCong (N→TDer dv=)
-- N→TDer {njudgment Γ _} (apr C (prev congruencerule) []) = UUCong
-- N→TDer {njudgment Γ _} (apr C (prev (prev congruencerule)) {js = [] , ◇ ⊢ A == A' , (◇ , _) ⊢ B == B' , (◇ ⊢ f == f' :> _) , (◇ ⊢ a == a' :> _)} ([] , dA= , dB= , df= , da=)
--   {{(((((tt , (tt , tt)) , ((tt , refl) , tt)) , (tt , (refl , tt))) , (tt , (refl , tt))) , tt)}})
--    = congTmEqTy! (N→T-Subst B a) (AppCong (N→TDer dA=) (N→TDer dB=) (congTmEqTy (ap (pi (N→T A)) (ap N→T Subst-insert-idMor)) (N→TDer df=)) (N→TDer da=))
-- N→TDer {njudgment Γ _} (apr C (prev (prev (prev congruencerule))) {js = [] , ◇ ⊢ A == A' , ((◇ , A) ⊢ B == B') , ((◇ , A) ⊢ u == u' :> B'')} ([] , dA= , dB= , du=) {{(((tt , (tt , tt)) , ((tt , refl) , tt)) , ((tt , refl) , (refl , tt)) ) , tt}}) = congTmEqTy! (ap (pi (N→T A)) (ap N→T Subst-insert-idMor)) (LamCong (N→TDer dA=) (N→TDer dB=) (congTmEqTy (ap N→T Subst-insert-idMor) (N→TDer du=)))
-- N→TDer {njudgment Γ _} (apr C (prev (prev (prev (prev congruencerule)))) {js = [] , ◇ ⊢ A == A' , (◇ , ._) ⊢ B == B'} ([] , dA= , dB=) {{(((tt , (tt , tt)) , ((tt , refl) , tt)) , tt)}}) = PiCong (N→TDer dA=) (N→TDer dB=)
-- N→TDer {njudgment Γ _} (apr Eq equalityrule js-der) = {!Eta!}
N→TDer {njudgment Γ _} (apr Eq (prev equalityrule) {js = [] , (◇ ⊢ A) , ((◇ , _) ⊢ B) , ((◇ , _) ⊢ u :> _) , (◇ ⊢ a :> _)} ([] , dA , dB , du , da)
  {{(((((tt , (tt , tt)) , ((tt , refl) , tt)) , ((tt , refl) , (refl , tt))) , (tt , (refl , tt))) , tt)}})
   = {!da --jdef --congTmEq! ? ? ? (BetaPi (N→TDer dA) (N→TDer dB) (congTmTy (ap N→T Subst-insert-idMor) (N→TDer du)) (N→TDer da))!}
