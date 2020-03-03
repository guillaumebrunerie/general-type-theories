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

prev^ : {n : ℕ} (m : ℕ) → WeakPos (n + m)
prev^ zero = last
prev^ {n} (suc m) = prev (prev^ {n} m)

-- ap= : {A B : Set} (f : A → B) {a b : A} → a === b → f a === f b
-- ap= f refl = refl

-- rew : {k : ℕ} (n m : ℕ) → weakenWeakPos2 (prev^ {k} m) ≡ prev^ {k} (m + n)
-- rew zero m = refl
-- rew (suc n) m = ap prev (rew n m)

-- Subst1-weakenV : {Σ : Signature} {n m : ℕ} {p : (n + m) ≤ (suc n + m)} (x : VarPos (n + m)) {f : N.TmExpr Σ n} → Subst1 m (var (N.weakenV {{p}} (prev^ {n} m) x)) f ≡ var x
-- Subst1-weakenV {m = zero} {≤S ≤r} x = refl
-- Subst1-weakenV {m = zero} {≤S (≤S p)} x = {!!}
-- --Subst1-weakenV {m = zero} {≤S (≤S p)} x = {!p absurd!}
-- Subst1-weakenV {m = suc m} last = refl
-- Subst1-weakenV {m = suc m} (prev x) = ap (N.weaken last) (Subst1-weakenV {m = m} x)

-- Subst1-weaken  : {Σ : Signature} {n m : ℕ} {k : SyntaxSort} {{p : {!!}}} (e : N.Expr Σ (n + m) k) {f : N.TmExpr Σ n} → Subst1 m (N.weaken {{p}} (prev^ {n} m) e) f ≡ e
-- Subst1-weakenA : {Σ : Signature} {n m : ℕ} {ar : SyntaxArityArgs} (es : N.Args Σ (n + m) ar) {f : N.TmExpr Σ n} → Subst1A m (N.weakenA {{≤+ m {{≤S ≤r}}}} (prev^ {n} m) es) f ≡ es



-- Subst1-weaken {n = n} {m} (var x) = Subst1-weakenV {n = n} {m} x
-- Subst1-weaken {m = zero} (sym s x) = ap (sym s) (Subst1-weakenA x)
-- Subst1-weaken {m = suc m} (sym s x) = ap (sym s) (Subst1-weakenA x)

-- Subst1V-weaken-varlast : {Σ : Signature} {n : ℕ} (x : VarPos (suc n)) → Subst1 {Σ} 0 (var (N.weakenV {{≤S ≤r}} (prev last) x)) (var last) ≡ var x
-- Subst1V-weaken-varlast last = refl
-- Subst1V-weaken-varlast (prev x) = refl

-- Subst1-weaken-varlast : {Σ : Signature} {n : ℕ} {k : SyntaxSort} (e : N.Expr Σ (suc n) k) → Subst1 0 (N.weaken {{≤S ≤r}} (prev last) e) (var last) ≡ e
-- Subst1A-weaken-varlast : {Σ : Signature} {n : ℕ} {ar : SyntaxArityArgs} (es : N.Args Σ (suc n) ar) → Subst1A 0 (N.weakenA {{≤S ≤r}} (prev last) es) (var last) ≡ es

-- Subst1-weaken-varlast (var x) = Subst1V-weaken-varlast x
-- Subst1-weaken-varlast (sym s es) = ap (sym s) (Subst1A-weaken-varlast es)

-- lemmaa : {Σ : Signature} {k : SyntaxSort} (x : N.Expr Σ (suc n + m) k) → tr! (assoc {suc n} {0} {m}) (Subst1 (0 + m) (tr (assoc {suc (suc n)} {0} {m}) (N.weaken ⦃ ≤+ m {suc n} {suc (suc n)} ⦄ (weakenWeakPos2 {{≤-+ {suc n} {m}}} (prev last)) x)) (var last)) ≡ x
-- lemmaA : {Σ : Signature} {args : SyntaxArityArgs} (x : N.Args Σ (suc n + m) args) → trA (! (assoc {suc n} {0} {m})) (Subst1A (0 + m) (trA (assoc {suc (suc n)} {0} {m}) (N.weakenA ⦃ ≤+ m {suc n} {suc (suc n)} ⦄ (weakenWeakPos2 {{≤-+ {suc n} {m}}} (prev last)) x)) (var last)) ≡ x

-- lemmaa (var x) = {!!}
-- lemmaa (sym s x) = ap (sym s) {!!}

-- lemmaA [] = refl
-- lemmaA (xs , x) = ap2 _,_ (lemmaA xs) {!lemmaa x!}

-- Subst1A-weaken-varlast [] = refl
-- Subst1A-weaken-varlast (es , x) = ap2 _,_ (Subst1A-weaken-varlast es) (lemmaa x)

--≤+-assoc : (n + m) + k

-- Subst1-weakenA [] = refl
-- Subst1-weakenA {n = n} {m} (_,_ {m = k} es e) {f} = ap2 _,_ (Subst1-weakenA es) (ap (λ x → Subst1 (m + k) (N.weaken {{{!!}}} x e) f) (rew k m) ∙ Subst1-weaken {m = m + k} e {f})

-- Subst1-weakenV : {Σ : Signature} {n : ℕ} {p : _} (x : VarPos (suc n)) {f : N.Expr Σ (suc n) Tm} → Subst1 0 (var (N.weakenVL {{p}} x)) f ≡ var x
-- Subst1-weakenV {p = ≤S ≤r} x = refl
-- Subst1-weakenV {p = ≤S (≤S p)} x = {!p absurd!}

-- Subst1-weaken : {Σ : Signature} {n : ℕ} {k : SyntaxSort} {p : _} (e : N.Expr Σ (suc n) k) {f : N.Expr Σ (suc n) Tm} → Subst1 0 (N.weaken {{p}} last e) f ≡ e
-- Subst1-weakenA : {Σ : Signature} {n : ℕ} {args : SyntaxArityArgs} {p : _} (es : N.Args Σ (suc n) args) {f : N.Expr Σ (suc n) Tm} → Subst1A 0 (N.weakenA {{p}} last es) f ≡ es

-- Subst1-weaken {p = p} (var x) {f = f} = Subst1-weakenV {p = p} x {f = f}
-- Subst1-weaken (sym s x) = ap (sym s) (Subst1-weakenA x)

-- Subst1-weakenA [] = refl
-- Subst1-weakenA (es , x) = ap2 _,_ (Subst1-weakenA es) {!!}

-- postulate
--  Subst1-varlast' : {Σ : Signature} {n l : ℕ} (m : ℕ) {k : SyntaxSort} {p : _} (e : N.Expr Σ (suc (suc n) + m) k) → Subst1 m (N.weaken {{p}} last e) (var (last {l})) ≡ N.weaken {{{!≤S ≤r!}}} last (Subst1 m e (var last))
--  Subst1-varlast' : {Σ : Signature} {n m : ℕ} {k : SyntaxSort} {p : _} (e : N.Expr Σ {!m!} k) → Subst1 0 (N.weaken {{p}} last e) (var (last {{!m!}})) ≡ e
-- Subst1-varlast zero (var x) = {!!}
-- Subst1-varlast (suc m) (var last) = {!!}
-- Subst1-varlast (suc m) (var (prev x)) = {!!}
-- Subst1-varlast zero (sym s x) = ap (sym s) {!!}
-- Subst1-varlast (suc m) (sym s x) = ap (sym s) {!!}

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

lemma' : {l : ListProp} {p : pf l → ListProp} → ΣP (pf l) (λ x → pf (p x)) → pf (l , p)
lemma' {[]} (p , q) = q
lemma' {[ x ]} (p , q) = p , q
lemma' {l , x} (p , q) = p , q

lemmax : {n : ℕ} (k : VarPos n) (Γ : T.Ctx n)
         → pf (listIsDefined (N.get (VarPos→ℕ k) (T→NCtx Γ)) ,
            (λ x → [ snd (N.get (VarPos→ℕ k) (T→NCtx Γ) $ x) ≡ T→N (T.get k Γ) ] ,
                   (λ x₁ → [])))
lemmax last (Γ , A) = weaken-comm last , tt
lemmax (prev k) (Γ , A) = lemma' {l = listIsDefined (N.get (VarPos→ℕ k) (T→NCtx Γ))} (fst (lemma {l = listIsDefined (N.get (VarPos→ℕ k) (T→NCtx Γ))} (lemmax k Γ)) , tt) , ((ap (N.weaken last) (snd-VarPos→ℕ k Γ) ∙ weaken-comm last) , tt)

Mor-insert : {Σ : Signature} (x : WeakPos m) (δ : N.Mor Σ n m) (u : N.TmExpr Σ n) → N.Mor Σ n (suc m)
Mor-insert last δ u = (δ , u)
Mor-insert (prev x) (δ , v) u = (Mor-insert x δ u , v)

Mor-remove : {Σ : Signature} (x : VarPos m) (δ : N.Mor Σ n m) → N.Mor Σ n (pred m)
Mor-remove last (δ , u) = δ
Mor-remove {m = suc (suc m)} (prev x) (δ , u) = (Mor-remove x δ , u)

thing : WeakPos n → VarPos (suc n)
thing last = last
thing (prev x) = prev (thing x)

Subst-insert2 : {k : SyntaxSort} {n : ℕ} {B : N.Expr Σ n k} {x : WeakPos n} {δ : N.Mor Σ m (suc n)} → SubstMor (N.weaken x B) δ ≡ SubstMor B (Mor-remove (thing x) δ)
SubstA-insert2 : {args : SyntaxArityArgs} {n : ℕ} {Bs : N.Args Σ n args} {x : WeakPos n} {δ : N.Mor Σ m (suc n)} → SubstAMor (N.weakenA x Bs) δ ≡ SubstAMor Bs (Mor-remove (thing x) δ)

Subst-insert2 {B = var x} = {!!}
Subst-insert2 {B = sym s x} = ap (sym s) SubstA-insert2

SubstA-insert2 {Bs = []} = refl
SubstA-insert2 {Bs = Bs , v} {x = x} {δ = δ} = ap2 _,_ SubstA-insert2 {!Subst-insert2 {B = v} {x = weakenWeakPos2 {{?}} x} {δ = N.weakenMor+ δ} ∙ ?!}

thingx : {Σ : Signature} {m : ℕ} {n k : ℕ} {x : WeakPos n} {δ : N.Mor Σ k n} {u : N.TmExpr Σ k} → N.Mor Σ (k + m) (suc (n + m))
thingx {Σ} {m} {n} {k} {x} {δ} {u} = Mor-insert (weakenWeakPos2 x) (N.weakenMor+ m δ) (N.weakenL u)

{-# REWRITE +O-rewrite #-}
{-# REWRITE +S-rewrite #-}
{-# REWRITE assoc #-}

lm : {Σ : Signature} {m : ℕ} {n k : ℕ} {x : WeakPos n} {δ : N.Mor Σ k n} {u : N.TmExpr Σ k} {δ' : N.Mor Σ (k + m) (n + m)} → N.weakenMor+ m δ ≡ δ' → N.weakenMor+ m (Mor-insert x δ u) ≡ Mor-insert (weakenWeakPos2 x) δ' (N.weaken last u)
lm refl = {!w!}

idMor+= : {Σ : Signature} (m : ℕ) → N.weakenMor+ {Σ} m {n = n} idMor ≡ idMor
idMor+= zero = refl
idMor+= (suc m) = ap2 _,_ (ap N.weakenMor (idMor+= m)) refl

SubstV-insert : {n : ℕ} {y : VarPos (suc n)} {x : WeakPos (suc n)} {u : N.TmExpr Σ (suc n)} {p : _} → SubstMor (var (N.weakenV {{p}} x y)) (Mor-insert x idMor u) ≡ var y
SubstV-insert {y = last} {x = last} {p = ≤S ≤r} = refl
SubstV-insert {y = prev y} {x = last} {p = ≤S ≤r} = {!!}
SubstV-insert {x = last} {p = ≤S (≤S p)} = {!impossible!}
SubstV-insert {y = last} {x = prev x} = refl
SubstV-insert {y = prev y} {x = prev x} = {!!}

Subst-insert  : {k : SyntaxSort} {n : ℕ} {e : N.Expr Σ (suc n) k} {x : WeakPos (suc n)} {u : N.TmExpr Σ (suc n)} {p : _} → SubstMor (N.weaken {{p}} x e) (Mor-insert x idMor u) ≡ e
SubstA-insert : {args : SyntaxArityArgs} {n : ℕ} {es : N.Args Σ (suc n) args} {x : WeakPos (suc n)} {u : N.TmExpr Σ (suc n)} {p : _} → SubstAMor (N.weakenA {{p}} x es) (Mor-insert x idMor u) ≡ es

Subst-insert {e = var x} {x = x'} = SubstV-insert {x = x'}
Subst-insert {e = sym s x} = ap (sym s) SubstA-insert

SubstA-insert {es = []} = refl
SubstA-insert {args} {n} {es = _,_ {m = m} es e} {x = x} {u = u} {p = p} =
  ap2 _,_ SubstA-insert (ap (SubstMor (N.weaken {{≤+ m {suc n} {suc (suc n)} {{p}}}} (weakenWeakPos2 x) e)) (lm {m = m} {n = suc n} {k = suc n} {x = x} {u = u} (idMor+= m)) ∙ Subst-insert {e = e} {x = weakenWeakPos2 x})

-- Subst-insert  : {k : SyntaxSort} {n : ℕ} {B : N.Expr Σ (suc n) k} → SubstMor (N.weaken (prev last) B) ((N.weakenMor idMor , var last) , var last) ≡ B
-- -- SubstA-insert : {args : SyntaxArityArgs} {n : ℕ} {Bs : N.Args Σ (suc n) args} → SubstAMor (N.weakenA (prev last) Bs) ((N.weakenMor idMor , var last) , var last) ≡ Bs

-- Subst-insert = Subst-insertx
-- -- Subst-insert {B = sym s x} = ap (sym s) SubstA-insert

-- SubstA-insert {Bs = []} = refl
-- SubstA-insert {Bs = Bs , x} = ap2 _,_ SubstA-insert {!Subst-insert {B = x}!}

T→NDer : {j : T.Judgment} → T.Derivable j → NDerivable (T→NJ j)
T→NDer (Var {Γ = Γ} k dA) = NDerivable=! (ap (λ x → njudgment (T→NCtx Γ) (◇ ⊢ var x :> T→N (T.get k Γ))) (fst-VarPos→ℕ k (T→NCtx Γ))) (apr S (var (VarPos→ℕ k)) ([] ,0Ty T→NDer dA) {{lemmax k Γ}})
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
  NDerivable=! (ap (λ z → njudgment _ (◇ ⊢ sym (prev (prev new)) ([] , T→N A , T→N B , T→N f , T→N a) :> z)) {!TODO!})
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

N→TJ : NJudgment → T.Judgment
N→TJ (njudgment Γ (◇ ⊢ A)) = N→TCtx Γ ⊢ N→T A
N→TJ (njudgment Γ (◇ ⊢ u :> A)) = N→TCtx Γ ⊢ N→T u :> N→T A
N→TJ (njudgment Γ (◇ ⊢ A == B)) = N→TCtx Γ ⊢ N→T A == N→T B
N→TJ (njudgment Γ (◇ ⊢ u == v :> A)) = N→TCtx Γ ⊢ N→T u == N→T v :> N→T A

congTmTy : {Γ : T.Ctx n} {u : T.TmExpr n} {A A' : T.TyExpr n} → A ≡ A' → T.Derivable (Γ ⊢ u :> A) → T.Derivable (Γ ⊢ u :> A')
congTmTy refl d = d

congTmTy! : {Γ : T.Ctx n} {u : T.TmExpr n} {A A' : T.TyExpr n} → A' ≡ A → T.Derivable (Γ ⊢ u :> A) → T.Derivable (Γ ⊢ u :> A')
congTmTy! refl d = d

congTmEqTy : {Γ : T.Ctx n} {u u' : T.TmExpr n} {A A' : T.TyExpr n} → A ≡ A' → T.Derivable (Γ ⊢ u == u' :> A) → T.Derivable (Γ ⊢ u == u' :> A')
congTmEqTy refl d = d

congTmEqTy! : {Γ : T.Ctx n} {u u' : T.TmExpr n} {A A' : T.TyExpr n} → A' ≡ A → T.Derivable (Γ ⊢ u == u' :> A) → T.Derivable (Γ ⊢ u == u' :> A')
congTmEqTy! refl d = d

N→TDer : {j : NJudgment} → NDerivable j → T.Derivable (N→TJ j)
N→TDer {njudgment Γ _} (apr S (var k) {js = [] , ◇ ⊢ A} ([] , dA) {{def}}) = {!def!}
N→TDer {njudgment Γ _} (apr S conv {js = [] , ◇ ⊢ u :> A , ◇ ⊢ A == B} ([] , du , dA=) {{refl , tt}}) = Conv (N→TDer du) (N→TDer dA=)
N→TDer {njudgment Γ _} (apr S convEq {js = [] , ◇ ⊢ u == v :> A , ◇ ⊢ A == B} ([] , du= , dA=) {{refl , tt}}) = ConvEq (N→TDer du=) (N→TDer dA=)
N→TDer {njudgment Γ _} (apr S tyRefl {js = [] , ◇ ⊢ A} ([] , dA)) = TyRefl (N→TDer dA)
N→TDer {njudgment Γ _} (apr S tySymm {js = [] , ◇ ⊢ A == B} ([] , dA=)) = TySymm (N→TDer dA=)
N→TDer {njudgment Γ _} (apr S tyTran {js = [] , ◇ ⊢ A == B , ◇ ⊢ B == D} ([] , dA= , dB=) {{refl , tt}}) = TyTran (N→TDer dA=) (N→TDer dB=)
N→TDer {njudgment Γ _} (apr S tmRefl {js = [] , ◇ ⊢ u :> A} ([] , du)) = TmRefl (N→TDer du)
N→TDer {njudgment Γ _} (apr S tmSymm {js = [] , ◇ ⊢ u == v :> A} ([] , du=)) = TmSymm (N→TDer du=)
N→TDer {njudgment Γ _} (apr S tmTran {js = [] , ◇ ⊢ u == v :> A , ◇ ⊢ v == w :> A} ([] , du= , dv=) {{refl , (refl , tt)}}) = TmTran (N→TDer du=) (N→TDer dv=)
N→TDer {njudgment Γ _} (apr T typingrule {js = [] , (◇ ⊢ v :> _)} ([] , dv) {{(tt , (refl , tt)) , tt }}) = El (N→TDer dv)
N→TDer {njudgment Γ _} (apr T (prev typingrule) []) = UU
--N→TDer {njudgment Γ _} (apr T (prev (prev typingrule)) {js = [] , ◇ ⊢ A , (◇ , _) ⊢ B , (◇ ⊢ f :> _) , (◇ ⊢ a :> _)} ([] , dA , dB , df , da)
--                            {{(((((tt , tt) , ((tt , refl) , tt)) , (tt , (refl , tt))) , (tt , (refl , tt))) , tt)}}) = {!N→TDer df --cong --App (N→TDer dA) (N→TDer dB) {!(N→TDer df)!} (N→TDer da)!}
-- N→TDer {njudgment Γ _} (apr T (prev (prev (prev typingrule))) {js = [] , ◇ ⊢ A , ((◇ , A) ⊢ B) , ((◇ , A) ⊢ u :> B)} ([] , dA , dB , du) {{(((tt , tt) , ((tt , refl) , tt)) , ((tt , refl) , (refl , tt)) ) , tt}})
--   = congTmTy! (ap (pi (N→T A)) (ap N→T Subst-insert)) (Lam (N→TDer dA) (N→TDer dB) (congTmTy (ap N→T Subst-insert) (N→TDer du)))
N→TDer {njudgment Γ _} (apr T (prev (prev (prev (prev typingrule)))) {js = [] , ◇ ⊢ A , (◇ , ._) ⊢ B} ([] , dA , dB) {{((tt , tt) , ((tt , refl) , tt)) , tt}}) = Pi (N→TDer dA) (N→TDer dB)
N→TDer {njudgment Γ _} (apr C congruencerule {js = [] , ◇ ⊢ v == v' :> _} ([] , dv=) {{((tt , (refl , tt)) , tt)}}) = ElCong (N→TDer dv=)
N→TDer {njudgment Γ _} (apr C (prev congruencerule) []) = UUCong
N→TDer {njudgment Γ _} (apr C (prev (prev congruencerule)) js-der) = {!AppCong!}
N→TDer {njudgment Γ _} (apr C (prev (prev (prev congruencerule))) {js = [] , ◇ ⊢ A == A' , ((◇ , A) ⊢ B == B') , ((◇ , A) ⊢ u == u' :> B'')} ([] , dA= , dB= , du=) {{(((tt , tt) , ((tt , refl) , tt)) , ((tt , refl) , (refl , tt)) ) , tt}}) = congTmEqTy! (ap (pi (N→T A)) (ap N→T Subst-insert)) (LamCong (N→TDer dA=) (N→TDer dB=) (congTmEqTy (ap N→T Subst-insert) (N→TDer du=)))
N→TDer {njudgment Γ _} (apr C (prev (prev (prev (prev congruencerule)))) {js = [] , ◇ ⊢ A == A' , (◇ , ._) ⊢ B == B'} ([] , dA= , dB=) {{(((tt , tt) , ((tt , refl) , tt)) , tt)}}) = PiCong (N→TDer dA=) (N→TDer dB=)
N→TDer {njudgment Γ _} (apr Eq equalityrule js-der) = {!Eta!}
N→TDer {njudgment Γ _} (apr Eq (prev equalityrule) js-der) = {!Beta!}
