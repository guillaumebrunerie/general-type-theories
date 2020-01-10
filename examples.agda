{-# OPTIONS --rewriting --prop #-}

open import common
open import syntx
open import derivability
open import structuralrules
open import typingrules
open import typetheories

module _ where

{- Π-Types + a dependent type -}

module _ where
  TypingRuleΠ : TypingRule (TTDer ◇) ([] , (0 , Ty) , (1 , Ty)) Ty
  TypingRuleΠ = Ty ([] , Ty []
                       , Ty ([] , (sym 0 [] / apr 0 [])))

  ΠUEl-TT1 : TypeTheory
  ΠUEl-TT1 = ◇ , TypingRuleΠ

  TypingRuleλ : TypingRule (TTDer ΠUEl-TT1) ([] , (0 , Ty) , (1 , Ty) , (1 , Tm)) Tm
  TypingRuleλ = Tm ([] , Ty []
                       , Ty ([] , (sym 0 [] / apr 0 []))
                       , Tm ([] , (sym 1 [] / apr 1 []))
                            (sym 1 ([] , sym 0 []) /
                             apr 1 (_,_ {j = ◇ ⊢ _ :> _} [] (apr 0 []))))
                   (sym 3 ([] , sym 2 [] , sym 1 ([] , var last)) /
                    apr 3 ([] , apr 2 [] , flat {j = (◇ , _) ⊢ _} (apr 1 ([] , apr (str (var 0)) ([] , apr 2 [])))))

  ΠUEl-TT2 : TypeTheory
  ΠUEl-TT2 = ΠUEl-TT1 , TypingRuleλ

  TypingRuleapp : TypingRule (TTDer ΠUEl-TT2) ([] , (0 , Ty) , (1 , Ty) , (0 , Tm) , (0 , Tm)) Tm
  TypingRuleapp = Tm ([] , Ty []
                         , Ty ([] , (sym 0 [] / apr 0 []))
                         , Tm [] (sym 3 ([] , sym 1 [] , sym 0 ([] , var last)) /
                                  apr 3 ([] , apr 1 [] , flat {j = (◇ , _) ⊢ _} (apr 0 ([] , apr (str (var 0)) ([] , apr 1 [])))))
                         , Tm [] (sym 2 [] / apr 2 []))
                     (sym 2 ([] , sym 0 []) /
                      apr 2 ([] , apr 0 []))

  ΠUEl-TT3 : TypeTheory
  ΠUEl-TT3 = ΠUEl-TT2 , TypingRuleapp

  TypingRuleBeta : EqualityRule (TTDer ΠUEl-TT3) ([] , (0 , Ty) , (1 , Ty) , (1 , Tm) , (0 , Tm)) Tm=
  TypingRuleBeta = Tm= ([] , Ty []
                           , Ty ([] , (sym 0 [] / apr 0 []))
                           , Tm ([] , (sym 1 [] / apr 1 []))
                                (sym 1 ([] , sym 0 []) /
                                 apr 1 (_,_ {j = ◇ ⊢ _ :> _} [] (apr 0 [])))
                           , Tm [] (sym 2 [] / apr 2 []))
                       (sym 2 ([] , sym 0 []) <:
                         sym 4 ([] , sym 3 [] , sym 2 ([] , var last) , sym 5 ([] , sym 3 [] , sym 2 ([] , var last) , sym 1 ([] , var last)) , sym 0 []) /
                         {!apr 4 ([] , apr 3 [] , flat {j = (◇ , _) ⊢ _} (apr 2 ([] , apr (str (var 0)) ([] , apr 3 []))) , apr 5 ([] , apr 3 [] , flat {j = (◇ , _) ⊢ _} (apr 2 ([] , apr (str (var 0)) ([] , apr 3 []))) , flat {j = (◇ , _) ⊢ _ :> _} ?) , apr 0 [])!}
                         // sym 1 ([] , sym 0 []) / apr 1 ([] , apr 0 []))

  ΠUEl-TT4 : TypeTheory
  ΠUEl-TT4 = ΠUEl-TT3 ,= TypingRuleBeta

  TypingRuleU : TypingRule (TTDer ΠUEl-TT4) [] Ty
  TypingRuleU = Ty []

  ΠUEl-TT5 : TypeTheory
  ΠUEl-TT5 = ΠUEl-TT4 , TypingRuleU
  
  TypingRuleEl : TypingRule (TTDer ΠUEl-TT5) ([] , (0 , Tm)) Ty
  TypingRuleEl = Ty ([] , Tm [] (sym 0 [] / apr 0 []))

  ΠUEl-TT : TypeTheory
  ΠUEl-TT = ΠUEl-TT5 , TypingRuleEl


{- Natural numbers -}

module _ where
  TypingRuleℕ : TypingRule (TTDer ◇) [] Ty
  TypingRuleℕ = Ty []

  ℕ-TT0 : TypeTheory
  ℕ-TT0 = ◇ , TypingRuleℕ

  TypingRule0 : TypingRule (TTDer ℕ-TT0) [] Tm
  TypingRule0 = Tm [] (sym 0 [] / apr 0 [])

  ℕ-TT1 : TypeTheory
  ℕ-TT1 = ℕ-TT0 , TypingRule0

  TypingRuleS : TypingRule (TTDer ℕ-TT1) ([] , (0 , Tm)) Tm
  TypingRuleS = Tm ([] , Tm [] (sym 1 [] / apr 1 []))
                   (sym 2 [] / apr 2 [])

  ℕ-TT2 : TypeTheory
  ℕ-TT2 = ℕ-TT1 , TypingRuleS

  TypingRuleℕ-elim : TypingRule (TTDer ℕ-TT2) ([] , (1 , Ty) , (0 , Tm) , (2 , Tm) , (0 , Tm)) Tm
  TypingRuleℕ-elim = Tm ([] , Ty ([] , sym 2 [] / apr 2 [])
                            , Tm [] (sym 3 [] / apr 3 [])
                            , Tm ([] , sym 4 [] / apr 4 []
                                     , sym 2 ([] , sym 0 []) / apr 2 ([] , apr 0 []))
                                 (sym 3 ([] , sym 4 ([] , sym 1 [])) /
                                  apr 3 ([] , apr 4 ([] , apr 1 [])))
                            , Tm [] (sym 5 [] / apr 5 []))
                        (sym 3 ([] , (sym 0 [])) / apr 3 ([] , apr 0 []))

  ℕ-TT : TypeTheory
  ℕ-TT = ℕ-TT2 , TypingRuleℕ-elim
