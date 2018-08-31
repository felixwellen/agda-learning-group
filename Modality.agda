{-# OPTIONS --without-K #-}

module Modality where

{- we postulate a mondic modality in this file -} 

open import BasicDefinitions public

postulate
  ○ : ∀ {i} → U i → U i              -- \ci
  η : ∀ {i} {A : U i} → A → ○ A      -- \eta

{- 
  we break the list of axioms here, to make some definitions
  we need in the last axiom below
-}

η-at : ∀ {i} (A : U i) → A → ○ A
η-at A = η

_is-modal : ∀ {i} (A : U i) → U i
A is-modal = (η-at A) is-an-equivalence

{-
  the universe of modal types
-}

U-○ : ∀ {i} → U (lsuc i)
U-○ = Σ (λ (A : U _) → A is-modal)

postulate
  {- 
    For all modal dependent types P : ○ A → U-○,
    there is an equivalence:
    _∘η : Π P → Π (P ∘ η)
    The 'unique-elimination' below has a ' at the end
    of its name. This indicates, there is another version of 
    it, which will be the 'real' version.
    After some preliminary work, we will derive this 'real'
    version.
  -}
  unique-elimination' :
    ∀ {i} {A : U i} (P : ○ A → U i) 
    → (λ (s : (x : ○ A) → ○ (P x)) → (λ (x : A) → s (η x))) is-an-equivalence

{-
  we will derive a preliminary recursion from that
-}
module recursion' {i} {A B : U i} (f : A → ○ B) where 
  open _is-an-equivalence (unique-elimination' (λ (x : ○ A) → B))
    renaming (η to left-invertibility; ε to right-invertibility)
  
  ○-recursion : (○ A → ○ B)
  ○-recursion = inverse f

  ○-compute : 
    (x : A) → ○-recursion (η x) ≈ f(x)
  ○-compute x = ap (λ g → g x) (right-invertibility f) 

  ○-uniqueness : (g : ○ A → ○ B)
    → g ∘ η ⇒ f → g ⇒ ○-recursion
  ○-uniqueness g ζ x =
      g(x)
    ≈⟨ ap (λ g → g x) (ap (λ F → F g) (fun-ext left-invertibility)) ⁻¹ ⟩
      inverse (g ∘ η) x 
    ≈⟨ ap (λ f → f x) (ap inverse (fun-ext ζ)) ⟩
      (inverse f) x
    ≈⟨ refl ⟩
      ○-recursion x
    ≈∎

{-
  we will continue with functoriality of ○ and naturality of η
-}
○→ : ∀ {i} {A B : U i}
  → (f : A → B) → (○ A → ○ B)
○→ f =
  let
    open recursion' (η ∘ f)
  in ○-recursion



η-is-natural : ∀ {i} {A B : U i}
  → (f : A → B)
  → ○→ f ∘ η ⇒ η ∘ f
η-is-natural f =
  let
    open recursion' (η ∘ f)
  in ○-compute

{- idempotency -}
○-ed-types-are-modal :
    ∀ {i} {A : U i}
    → (○ A) is-modal
○-ed-types-are-modal =
    let
      open recursion'
    in
      create-equivalence-proof
        η (○-recursion id)
        (○-compute id)
          (  ○-uniqueness η (η ∘ ○-recursion id) (λ x → ap η (○-compute id x))
          •⇒ ○-uniqueness η id (λ _ → refl) ⁻¹⇒ )

{-
  Now we repeat the unique-elimination axiom and the 
  recursion in a slightly more general way (i.e. replacing 
  one application of '○' with the condition of being modal):
-}

unique-elimination :
    ∀ {i} {A : U i} (P : ○ A → U i) (p : (x : ○ A) → (P x) is-modal) 
    → (λ (s : (x : ○ A) → P x) → (λ (x : A) → s (η x))) is-an-equivalence
unique-elimination P p =
  let
    φ : Π P ≃ Π (λ x → ○ (P x))
    φ = equivalenct-depedent-types-have-equivalent-Π P (λ z → ○ (P z)) (λ x → η is-an-equivalence-because (p x))
    old-elimination : Π (λ x → ○ (P x)) ≃ Π (λ y → ○ (P (η y)))
    old-elimination  = (λ s x → s (η x)) is-an-equivalence-because unique-elimination' P
    ψ : Π (λ y → (P (η y))) ≃ Π (λ y → ○ (P (η y)))
    ψ = equivalenct-depedent-types-have-equivalent-Π (λ y → P (η y)) (λ x → ○ (P (η x))) (λ x → η is-an-equivalence-because p (η x))
    commutes : (ψ ⁻¹→) ∘ (λ s x → s (η x)) ∘ (φ ≃→) ⇒ (λ s x → s (η x))
    commutes s = ap (ψ ⁻¹→) refl • (ψ ≃η) (λ x → s (η x))
  in equivalences-are-preserved-by-homotopy
     (λ s → (ψ ⁻¹→) (λ x → ((_≃_.e φ) s) (η x)))
     (λ (s : (x : ○ _) → P x) → λ x → s (η x))
     (_≃_.proof (ψ ⁻¹≃ ∘≃ old-elimination ∘≃ φ))
     commutes


{- we repeat our definitions for recursion rules.
   this time, for maps into a modal 'B'. -}
module recursion {i} {A : U i} {B : U i} (p : B is-modal) (f : A → B) where 
  open _is-an-equivalence (unique-elimination (λ (x : ○ A) → B) (λ _ → p))
    renaming (η to left-invertibility; ε to right-invertibility)

  open _is-an-equivalence (○-ed-types-are-modal {A = B})
    hiding (η ; ε) renaming (inverse to η-B⁻¹)

  ○-recursion : (○ A → B)
  ○-recursion = inverse f

  ○-compute : 
    (x : A) → ○-recursion (η x) ≈ f(x)
  ○-compute x = ap (λ g → g x) (right-invertibility f) 

  ○-uniqueness : (g : ○ A → B)
    → g ∘ η ⇒ f → g ⇒ ○-recursion
  ○-uniqueness g ζ x =
      g(x)
    ≈⟨ ap (λ g → g x) (ap (λ F → F g) (fun-ext left-invertibility)) ⁻¹ ⟩
      inverse (g ∘ η) x 
    ≈⟨ ap (λ f → f x) (ap inverse (fun-ext ζ)) ⟩
      (inverse f) x
    ≈⟨ refl ⟩
      ○-recursion x
    ≈∎

{-

  the next goals are various closure and preservation properties of 
  modalities:

  modal types are closed under 
  * identity types
  * Π of dependent types P : A → U-○
  * Σ of dependent types P : ○ A → U-○
  * pullbacks of modal cospans

  ○ preserves
  * 2-cells (○⇒)
  * equivalences (○≃)
  * products
  * or more general: ○ Σ (λ (x : A) → B(ηx)) ≃ Σ (λ (y : ○A) → ○B(y))

-}

{-
  We start with identity types.
  For x,y:A, look a the constant functions 

  x,y : x≈y → A

  And the projecting 2-cell

  (λ (γ : x≈y) → γ) : x ⇒ y

  ○-uniqueness tells us, that the constant functions

  x,y : ○(x≈y) → A

  must be equal as well, i.e. there is a 2-cell x ⇒ y, which is
  also a map φ : ○(x≈y) → x≈y, which will turn out to be an inverse to η
-}

open recursion

○-induce-2-cell : ∀ {i} {A B : U i} (p : B is-modal)
  → (f g : A → B)
  → f ⇒ g → ○-recursion p f ⇒ ○-recursion p g
○-induce-2-cell p f g ζ = ○-uniqueness p g (○-recursion p f) (○-compute p f •⇒ ζ)

{-
○-preserves-identity-types :
  ∀ {i} {A : U i} (p : A is-modal)
  → (x y : A) → (x ≈ y) is-modal
○-preserves-identity-types p x y =
  let
    φ : ○(x ≈ y) → x ≈ y
    φ = ○-uniqueness p (λ (_ : x ≈ y) → x) (λ (_ : ○(x ≈ y)) → x) (λ _ → refl)
      •⇒ ○-uniqueness p (λ (_ : x ≈ y) → x) (λ (_ : ○(x ≈ y)) → y) (λ (γ : x ≈ y) → γ ⁻¹) ⁻¹⇒ 
  in create-equivalence-proof η φ (λ γ → {!!}) {!!}

○⇒ : ∀ {i} {A B : U i} {f g : A → B}
  → f ⇒ g → ○→ f ⇒ ○→ g
○⇒ {f = f} {g = g} ζ x =
  let
    open recursion'
  in {!○-compute (η ∘ f) !}
-}

{- ... -}
