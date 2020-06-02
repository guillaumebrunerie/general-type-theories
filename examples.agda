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
                       , Ty ([] , (sym 0 [] / apr T 0 [])))

  ΠUEl-TT1 : TypeTheory
  ΠUEl-TT1 = ◇ , TypingRuleΠ

  TypingRuleλ : TypingRule (TTDer ΠUEl-TT1) ([] , (0 , Ty) , (1 , Ty) , (1 , Tm)) Tm
  TypingRuleλ = Tm ([] , Ty []
                       , Ty ([] , (sym 0 [] / apr T 0 []))
                       , Tm ([] , (sym 1 [] / apr T 1 []))
                            (sym   1 ([] ,    sym   0 []) /
                             apr T 1 ([] ,0Tm apr T 0 [])))
                   (sym   3 ([] ,    sym   2 [] ,    sym   1 ([] ,    var last)) /
                    apr T 3 ([] ,0Ty apr T 2 [] ,1Ty apr T 1 ([] ,0Tm apr S (var 0) ([] , apr T 2 []))))

  ΠUEl-TT2 : TypeTheory
  ΠUEl-TT2 = ΠUEl-TT1 , TypingRuleλ

  TypingRuleapp : TypingRule (TTDer ΠUEl-TT2) ([] , (0 , Ty) , (1 , Ty) , (0 , Tm) , (0 , Tm)) Tm
  TypingRuleapp = Tm ([] , Ty []
                         , Ty ([] , (sym 0 [] / apr T 0 []))
                         , Tm [] (sym 3 ([] ,    sym 1 [] ,    sym 0 ([] ,    var last)) /
                                  apr T 3 ([] ,0Ty apr T 1 [] ,1Ty apr T 0 ([] ,0Tm apr S (var 0) ([] , apr T 1 []))))
                         , Tm [] (sym 2 [] / apr T 2 []))
                     (sym 2 ([] ,    sym 0 []) /
                      apr T 2 ([] ,0Tm apr T 0 []))

  ΠUEl-TT3 : TypeTheory
  ΠUEl-TT3 = ΠUEl-TT2 , TypingRuleapp

  TypingRuleBeta : EqualityRule (TTDer ΠUEl-TT3) ([] , (0 , Ty) , (1 , Ty) , (1 , Tm) , (0 , Tm)) Tm
  TypingRuleBeta = Tm= ([] , Ty []
                           , Ty ([] , sym 0 [] / apr T 0 [])
                           , Tm ([] , sym 1 [] / apr T 1 [])
                                (sym 1 ([] ,    sym 0 []) /
                                 apr T 1 ([] ,0Tm apr T 0 []))
                           , Tm [] (sym 2 [] / apr T 2 []))
                       (sym 2 ([] , sym 0 []) <:
                         sym 4 ([] , sym 3 []
                                   , sym 2 ([] , var last)
                                   , sym 5 ([] , sym 3 [] , sym 2 ([] , var last) , sym 1 ([] , var last))
                                   , sym 0 []) /
                         apr T 4 ([]
                           ,0Ty apr T 3 []
                           ,1Ty apr T 2 ([] ,0Tm apr S (var 0) ([] ,0Ty apr T 3 []))
                           ,0Tm apr T 5 ([] ,0Ty apr T 3 []
                                            ,1Ty apr T 2 ([] ,0Tm apr S (var zero) ([] ,0Ty apr T 3 []))
                                            ,1Tm apr T 1 ([] ,0Tm apr S (var zero) ([] ,0Ty apr T 3 []))) {-{{((tt , (tt , tt)) , ((tt , refl) , tt)) , ((tt , refl) , (refl , tt)) , tt}}-}
                           ,0Tm apr T 0 []) {-{{((((tt , (tt , tt)) , ((tt , refl) , tt)) , (tt , (refl , tt))) , (tt , (refl , tt))) , tt}}-}
                        // sym 1 ([] , sym 0 [])
                         / apr T 1 ([] ,0Tm apr T 0 []))

  ΠUEl-TT4 : TypeTheory
  ΠUEl-TT4 = ΠUEl-TT3 ,= TypingRuleBeta

  TypingRuleEta : EqualityRule (TTDer ΠUEl-TT4) ([] , (0 , Ty) , (1 , Ty) , (0 , Tm)) Tm
  TypingRuleEta = Tm= ([] , Ty []
                          , Ty ([] , sym 0 [] / apr T 0 [])
                          , Tm [] (sym 4 ([] , sym 1 [] , sym 0 ([] , var last))
                                 / apr T 4 ([] ,0Ty apr T 1 [] ,1Ty apr T 0 ([] ,0Tm apr S (var 0) ([] ,0Ty apr T 1 [])))))
                      (sym 5 ([] , sym 2 [] , sym 1 ([] , var last))
                      <: sym 0 []
                      /  apr T 0 []
                      // sym 4 ([] , sym 2 [] , sym 1 ([] , var last) , sym 3 ([] , sym 2 [] , sym 1 ([] , var last) , sym 0 [] , var last))
                      /  apr T 4 ([] ,0Ty apr T 2 []
                                     ,1Ty apr T 1 ([] ,0Tm apr S (var 0) ([] ,0Ty apr T 2 []))
                                     ,1Tm apr T 3 ([] ,0Ty apr T 2 []
                                                      ,1Ty apr T 1 ([] ,0Tm apr S (var 0) ([] ,0Ty apr T 2 []))
                                                      ,0Tm apr T 0 []
                                                      ,0Tm apr S (var 0) ([] ,0Ty apr T 2 []))))

  ΠUEl-TT5 : TypeTheory
  ΠUEl-TT5 = ΠUEl-TT4 ,= TypingRuleEta

  TypingRuleU : TypingRule (TTDer ΠUEl-TT5) [] Ty
  TypingRuleU = Ty []

  ΠUEl-TT6 : TypeTheory
  ΠUEl-TT6 = ΠUEl-TT5 , TypingRuleU
  
  TypingRuleEl : TypingRule (TTDer ΠUEl-TT6) ([] , (0 , Tm)) Ty
  TypingRuleEl = Ty ([] , Tm [] (sym 0 [] / apr T 0 []))

  ΠUEl-TT : TypeTheory
  ΠUEl-TT = ΠUEl-TT6 , TypingRuleEl


-- {- Natural numbers -}

-- module _ where
--   TypingRuleℕ : TypingRule (TTDer ◇) [] Ty
--   TypingRuleℕ = Ty []

--   ℕ-TT0 : TypeTheory
--   ℕ-TT0 = ◇ , TypingRuleℕ

--   TypingRule0 : TypingRule (TTDer ℕ-TT0) [] Tm
--   TypingRule0 = Tm [] (sym 0 [] / apr T 0 [])

--   ℕ-TT1 : TypeTheory
--   ℕ-TT1 = ℕ-TT0 , TypingRule0

--   TypingRuleS : TypingRule (TTDer ℕ-TT1) ([] , (0 , Tm)) Tm
--   TypingRuleS = Tm ([] , Tm [] (sym 1 [] / apr T 1 []))
--                    (sym 2 [] / apr T 2 [])

--   ℕ-TT2 : TypeTheory
--   ℕ-TT2 = ℕ-TT1 , TypingRuleS

--   TypingRuleℕ-elim : TypingRule (TTDer ℕ-TT2) ([] , (1 , Ty) , (0 , Tm) , (2 , Tm) , (0 , Tm)) Tm
--   TypingRuleℕ-elim = Tm ([] , Ty ([] , sym 2 [] / apr T 2 [])
--                             , Tm [] (sym 0 ([] , sym 2 []) / apr T 0 ([] ,0Tm apr T 2 []))
--                             , Tm ([] , sym 4 [] / apr T 4 []
--                                      , sym 2 ([] , sym 0 []) / apr T 2 ([] ,0Tm apr T 0 []))
--                                  (sym 3 ([] , sym 4 ([] , sym 1 [])) /
--                                   apr T 3 ([] ,0Tm apr T 4 ([] ,0Tm apr T 1 [])))
--                             , Tm [] (sym 5 [] / apr T 5 []))
--                         (sym 3 ([] , (sym 0 [])) / apr T 3 ([] ,0Tm apr T 0 []))

--   ℕ-TT3 : TypeTheory
--   ℕ-TT3 = ℕ-TT2 , TypingRuleℕ-elim

--   TypingRuleℕ0-β : EqualityRule (TTDer ℕ-TT3) ([] , (1 , Ty) , (0 , Tm) , (2 , Tm)) Tm
--   TypingRuleℕ0-β = Tm= ([] , Ty ([] , (sym 3 [] / apr T 3 []))
--                            , Tm [] (sym 0 ([] , sym 3 []) / apr T 0 ([] ,0Tm apr T 3 []))
--                            , Tm ([] , (sym 5 [] / apr T 5 [])
--                                     , (sym 2 ([] , sym 0 []) / apr T 2 ([] ,0Tm apr T 0 [])))
--                                 (sym 3 ([] , sym 5 ([] , sym 1 [])) / apr T 3 ([] ,0Tm apr T 5 ([] ,0Tm apr T 1 []))))
--                        (sym 2 ([] , sym 5 []) <: sym 3 ([] , sym 2 ([] , var last) , sym 1 [] , sym 0 ([] , var (prev last) , var last) , sym 5 [])
--                                                  / apr T 3 ([] ,1Ty apr T 2 ([] ,0Tm apr S (var 0) ([] ,0Ty apr T 6 []))
--                                                                ,0Tm apr T 1 []
--                                                                ,2Tm apr T 0 ([] ,0Tm apr S (var 1) ([] ,0Ty apr T 6 [])
--                                                                                 ,0Tm apr S (var 0) ([] ,0Ty apr T 2 ([] ,0Tm apr S (var 1) ([] ,0Ty apr T 6 []))))
--                                                                ,0Tm apr T 5 [])
--                                                  // sym 1 []
--                                                  / apr T 1 [])

--   ℕ-TT4 : TypeTheory
--   ℕ-TT4 = ℕ-TT3 ,= TypingRuleℕ0-β

--   TypingRuleℕS-β : EqualityRule (TTDer ℕ-TT4) ([] , (1 , Ty) , (0 , Tm) , (2 , Tm) , (0 , Tm)) Tm
--   TypingRuleℕS-β = Tm= ([] , Ty ([] , (sym 3 [] / apr T 3 []))
--                            , Tm [] (sym 0 ([] , sym 3 []) / apr T 0 ([] ,0Tm apr T 3 []))
--                            , Tm ([] , (sym 5 [] / apr T 5 [])
--                                     , (sym 2 ([] , sym 0 []) / apr T 2 ([] ,0Tm apr T 0 [])))
--                                 (sym 3 ([] , sym 5 ([] , sym 1 [])) / apr T 3 ([] ,0Tm apr T 5 ([] ,0Tm apr T 1 [])))
--                            , Tm [] (sym 6 [] / apr T 6 []))
--                        (sym 3 ([] , sym 5 ([] , sym 0 []))
--                          <: sym 4 ([] , sym 3 ([] , var last) , sym 2 [] , sym 1 ([] , var (prev last) , var last) , sym 5 ([] , sym 0 []))
--                          / apr T 4 ([] ,1Ty apr T 3 ([] ,0Tm apr S (var 0) ([] ,0Ty apr T 7 [])) ,0Tm apr T 2 [] ,2Tm apr T 1 ([] ,0Tm apr S (var 1) ([] ,0Ty apr T 7 []) ,0Tm (apr S (var 0) ([] ,0Ty apr T 3 ([] ,0Tm apr S (var 1) ([] ,0Ty apr T 7 []))))) ,0Tm apr T 5 ([] ,0Tm apr T 0 []))
--                          // sym 1 ([] , sym 0 [] , sym 4 ([] , sym 3 ([] , var last) , sym 2 [] , sym 1 ([] , var (prev last) , var last) , sym 0 []))
--                          / apr T 1 ([] ,0Tm apr T 0 [] ,0Tm apr T 4 ([] ,1Ty apr T 3 ([] ,0Tm apr S (var 0) ([] ,0Ty apr T 7 [])) ,0Tm apr T 2 [] ,2Tm apr T 1 ([] ,0Tm apr S (var 1) ([] ,0Ty apr T 7 []) ,0Tm (apr S (var 0) ([] ,0Ty apr T 3 ([] ,0Tm apr S (var 1) ([] ,0Ty apr T 7 []))))) ,0Tm apr T 0 [])))

--   ℕ-TT5 : TypeTheory
--   ℕ-TT5 = ℕ-TT4 ,= TypingRuleℕS-β
