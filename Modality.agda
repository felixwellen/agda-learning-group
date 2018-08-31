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
    φ = equivalenct-depedent-types-have-equivalent-Π P (λ z → ○ (P z))
          (λ x → η is-an-equivalence-because (p x))
    old-elimination : Π (λ x → ○ (P x)) ≃ Π (λ y → ○ (P (η y)))
    old-elimination  = (λ s x → s (η x)) is-an-equivalence-because unique-elimination' P
    ψ : Π (λ y → (P (η y))) ≃ Π (λ y → ○ (P (η y)))
    ψ = equivalenct-depedent-types-have-equivalent-Π
          (λ y → P (η y))
          (λ x → ○ (P (η x)))
          (λ x → η is-an-equivalence-because p (η x))
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
  * (categorical) retracts 
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


open recursion

universal-property :
  ∀ {i} {A : U i} (B : U i) (p : B is-modal)
  → (λ (f : ○ A → B) → f ∘ η) is-an-equivalence
universal-property B p = unique-elimination (λ _ → B) (λ _ → p)

○-yoneda :
  ∀ {i} {A B : U i} (η' : A → B) (p : B is-modal)
  → ((C : U i) → (q : C is-modal) → (λ (f : B → C) → f ∘ η') is-an-equivalence)
  → ○ A ≃ B
○-yoneda {_} {A} {B} η' p B-is-universal =
  let
    {- we only need the universal property of B in these two cases -}
    E1 = (B-is-universal (○ A) ○-ed-types-are-modal)
    E2 = (B-is-universal B p)
    open _is-an-equivalence 
      renaming (η to left-invertibility; ε to right-invertibility)
    e = ○-recursion p η'
    e⁻¹ : B → ○ A
    e⁻¹ = inverse E1 η
    ξ : e⁻¹ ∘ η' ⇒ η
    ξ x = ap (λ f → f x) (right-invertibility E1 η)
    τ : (λ f → f ∘ η') (e ∘ e⁻¹) ≈ (λ f → f ∘ η') id
    τ = fun-ext (λ y → ap e (ξ y) • ○-compute p η' y)
  in e is-an-equivalence-because (create-equivalence-proof e e⁻¹
    (λ x →    (e⁻¹ ∘ e) x
            ≈⟨ ○-uniqueness ○-ed-types-are-modal
                  η (e⁻¹ ∘ e)
                  (λ a → ap e⁻¹ (○-compute p η' a) • ξ a) x ⟩
              ○-recursion ○-ed-types-are-modal η x
            ≈⟨ ○-uniqueness ○-ed-types-are-modal η id (λ _ → refl) x ⁻¹ ⟩
              x
            ≈∎)
    (λ x → ap (λ f → f x)
              (   left-invertibility E2 (e ∘ e⁻¹) ⁻¹
                • (ap (inverse E2) τ)
                • left-invertibility E2 id)))

{-
  we will continue with functoriality of ○ and naturality of η
-}
○→ : ∀ {i} {A B : U i}
  → (f : A → B) → (○ A → ○ B)
○→ f = ○-recursion ○-ed-types-are-modal (η ∘ f)

η-is-natural : ∀ {i} {A B : U i}
  → (f : A → B)
  → ○→ f ∘ η ⇒ η ∘ f
η-is-natural f = ○-compute ○-ed-types-are-modal (η ∘ f)

○-induce-2-cell : ∀ {i} {A B : U i} (p : B is-modal)
  → (f g : A → B)
  → f ⇒ g → ○-recursion p f ⇒ ○-recursion p g
○-induce-2-cell p f g ζ = ○-uniqueness p g (○-recursion p f) (○-compute p f •⇒ ζ)

○⇒ : ∀ {i} {A B : U i} {f g : A → B}
  → f ⇒ g → ○→ f ⇒ ○→ g
○⇒ {f = f} {g = g} ζ x = ○-induce-2-cell ○-ed-types-are-modal (η ∘ f) (η ∘ g) (λ _ → ap η (ζ _)) x

id-is-preserved :
  ∀ {i} {A : U i}
  → id ⇒ ○→ (id {A = A}) 
id-is-preserved {A = A} = ○-uniqueness ○-ed-types-are-modal η id (λ _ → refl)

○→-commutes-with-∘ :
  ∀ {i} {A B C : U i}
  → (f : A → B) → (g : B → C)
  → ○→ g ∘ ○→ f ⇒ ○→ (g ∘ f) 
○→-commutes-with-∘ f g = ○-uniqueness ○-ed-types-are-modal (η ∘ g ∘ f) (○→ g ∘ ○→ f)
  (λ x →
      (○→ g ∘ ○→ f ∘ η) x
    ≈⟨ ap (○→ g) (○-compute ○-ed-types-are-modal (η ∘ f) x) ⟩
      (○→ g ∘ η ∘ f) x
    ≈⟨ ○-compute ○-ed-types-are-modal (η ∘ g) (f x) ⟩ 
      (η ∘ g ∘ f) x
    ≈∎)

retracts-of-modal-types-are-modal :
  ∀ {i} {A B : U i} (p : B is-modal)
  → (ι : A → B) → (r : B → A) → (r ∘ ι ⇒ id)
  → A is-modal
retracts-of-modal-types-are-modal {_} {A} {B} p ι r ζ =
  let
    open _is-an-equivalence renaming (η to left-invertible; ε to right-invertible)
    η-B⁻¹ : ○ B → B
    η-B⁻¹ = inverse p
    η⁻¹ : ○ A → A
    η⁻¹ = r ∘ η-B⁻¹ ∘ ○→ ι
  in create-equivalence-proof η η⁻¹
    (λ a →
       (r ∘ η-B⁻¹ ∘ ○→ ι ∘ η) a
      ≈⟨ ap (r ∘ η-B⁻¹) (η-is-natural ι a)  ⟩
        (r ∘ η-B⁻¹ ∘ η ∘ ι) a
      ≈⟨ ap r (left-invertible p (ι a)) ⟩
        (r ∘ ι) a
      ≈⟨ ζ a ⟩ 
       a
      ≈∎)
    (λ x →
        (η ∘ r ∘ η-B⁻¹ ∘ ○→ ι) x
      ≈⟨ η-is-natural r ((η-B⁻¹ ∘ ○→ ι) x) ⁻¹ ⟩
        (○→ r ∘ η ∘ η-B⁻¹ ∘ ○→ ι) x
      ≈⟨ ap (○→ r) (right-invertible p (○→ ι x)) ⟩
        (○→ r ∘ ○→ ι) x
      ≈⟨ ○→-commutes-with-∘ ι r x ⟩
        ○→ (r ∘ ι) x
      ≈⟨ ○⇒ ζ x ⟩ 
        ○→ id x
      ≈⟨ id-is-preserved x ⁻¹ ⟩ 
        x
      ≈∎)

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
{-
○-preserves-identity-types :
  ∀ {i} {A : U i} (p : A is-modal)
  → (x y : A) → (x ≈ y) is-modal
○-preserves-identity-types p x y =
  let
    φ : (λ (_ : ○(x ≈ y)) → x) ⇒ (λ (_ : ○(x ≈ y)) → y)
    φ = {!!}
  in {!!}
-}


{- ... -}

