{-# OPTIONS --without-K #-}

module Modality where

{- we postulate a mondic modality in this file -} 

open import BasicDefinitions public

postulate
  ○ : ∀ {i} → U i → U i              -- \ci
  η : ∀ {i} {A : U i} → A → ○ A      -- \eta

{- 
  we break the list of axioms here, to make some definitions
  we need in the last axiom
-}

η-at : ∀ {i} (A : U i) → A → ○ A
η-at A = η

_is-○-modal : ∀ {i} (A : U i) → U i
A is-○-modal = (η-at A) is-an-equivalence

{-
  the universe of modal types
-}

U-○ : ∀ {i} → U (lsuc i)
U-○ = Σ (λ (A : U _) → A is-○-modal)

ν : ∀ {i} {A : U i} → (P : A → U-○) → (A → U i)
ν P = λ (x : _) →  Σπ₁ (P x)

postulate
  {- 
    For all modal dependent types P : ○ A → U-○,
    there is an equivalence:
    _∘η : Π P → Π (P ∘ η)
  -}
  unique-elimination :
    ∀ {i} {A : U i} (P : ○ A → U-○)
    → (λ (s : Π (ν P)) → (λ (x : A) → s (η x))) is-an-equivalence

