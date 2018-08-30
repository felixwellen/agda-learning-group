{-# OPTIONS --without-K #-}

open import UniversesPiSigma
open import Equality

module Equivalence where 
{- 
  we use half adjoint equivalences...
-}
record _is-an-equivalence {i j} {A : U i} {B : U j} (f : A → B) : U (i ⊔ j) where
  field
    inverse : B → A
    η : inverse ∘ f ⇒ id
    ε : f ∘ inverse ⇒ id 
    half-adjoint : (a : A) → ap f (η a) ≈ ε (f a)

infixl 4 _≃_                                                -- \simeq
record _≃_  {i j} (A : U i) (B : U j) : U (i ⊔ j) where
  constructor _is-an-equivalence-because_
  field 
    e : A → B
    proof : e is-an-equivalence


_≃→ : ∀ {i j} {A : U i} {B : U j} → A ≃ B → (A → B)
(e is-an-equivalence-because _) ≃→ = e

_⁻¹→ : ∀ {i j} {A : U i} {B : U j} → A ≃ B → (B → A)
(e is-an-equivalence-because record { inverse = inverse ; η = η ; ε = ε ; half-adjoint = half-adjoint }) ⁻¹→ = inverse

_≃η : ∀ {i j} {A : U i} {B : U j} → (e : A ≃ B) → (e ⁻¹→) ∘ (e ≃→) ⇒ id 
(_ is-an-equivalence-because record { inverse = _ ; η = η ; ε = _ ; half-adjoint = _ }) ≃η = η

_≃ε : ∀ {i j} {A : U i} {B : U j} → (e : A ≃ B) → (e ≃→) ∘ (e ⁻¹→) ⇒ id 
(_ is-an-equivalence-because record { inverse = _ ; η = _ ; ε = ε ; half-adjoint = _ }) ≃ε = ε



postulate
  ∘≃-proof : ∀ {i j k} {A : U i} {B : U j} {C : U k} (g : B ≃ C) (f : A ≃ B) → (_≃_.e g ∘ _≃_.e f) is-an-equivalence
  ⁻¹≃-proof : ∀ {i j} {A : U i} {B : U j} → (f : A ≃ B) → f ⁻¹→ is-an-equivalence

infixr 70 _∘≃_
_∘≃_ : ∀ {i j k} {A : U i} {B : U j} {C : U k} (g : B ≃ C) (f : A ≃ B) → A ≃ C
g ∘≃ f = (_≃_.e g ∘ _≃_.e f) is-an-equivalence-because (∘≃-proof g f)

infix 80 _⁻¹≃
_⁻¹≃ : ∀ {i j} {A : U i} {B : U j} → A ≃ B → B ≃ A
f ⁻¹≃ = (f ⁻¹→) is-an-equivalence-because (⁻¹≃-proof f)

{- 
  use hott-book thm 4.2.3 
-}
postulate
  create-equivalence-proof :
    ∀ {i j} {A : U i} {B : U j} (f : A → B)
    → (f⁻¹ : B → A) → (f⁻¹ ∘ f ⇒ id) → (f ∘ f⁻¹ ⇒ id) 
    → f is-an-equivalence
{-
private 
  naturality-for-invertibility-witnesses :
    ∀ {A B : U₀} (f : A → B) (f⁻¹ : B → A)
    → (η : f⁻¹ ∘ f ⇒ id) 
    → (x : A) → η (f⁻¹ (f x)) ≈ ap (f⁻¹ ∘ f) (η x) 
  naturality-for-invertibility-witnesses f f⁻¹ η x =
      η (f⁻¹ (f x))
    ≈⟨ refl-is-right-neutral _ ⟩
       η ((f⁻¹ ∘ f) x) • refl
    ≈⟨  ap (λ ζ → η ((f⁻¹ ∘ f) x) • ζ) (⁻¹-is-right-inversion (η x)) ⁻¹  ⟩
       η ((f⁻¹ ∘ f) x) • ((η x) • η x ⁻¹)
    ≈⟨ •-is-associative (η ((f⁻¹ ∘ f) x)) _ _  ⟩
      η ((f⁻¹ ∘ f) x) • η x • η x ⁻¹
    ≈⟨ ap (λ ζ → η ((f⁻¹ ∘ f) x) • ζ • η x ⁻¹) (id-has-trivial-application _ ⁻¹) ⟩
      η ((f⁻¹ ∘ f) x) • ap id (η x) • η x ⁻¹
    ≈⟨  ap (λ ζ → ζ • η x ⁻¹) (naturality-of-homotopies (f⁻¹ ∘ f) id η (η x))  ⟩
      ap (f⁻¹ ∘ f) (η x) • η x • η x ⁻¹
    ≈⟨  •-is-associative (ap (f⁻¹ ∘ f) (η x)) _ _ ⁻¹ ⟩
      ap (f⁻¹ ∘ f) (η x) • (η x • η x ⁻¹)
    ≈⟨ ap (λ ζ → ap (f⁻¹ ∘ f) (η x) • ζ) (⁻¹-is-right-inversion (η x)) ⟩
      ap (f⁻¹ ∘ f) (η x) • refl 
    ≈⟨ refl-is-right-neutral (ap (f⁻¹ ∘ f) (η x)) ⁻¹ ⟩
      ap (f⁻¹ ∘ f) (η x) 
    ≈∎
-}


id-as-equivalence : ∀ {i} {A : U i} → A ≃ A
id-as-equivalence = id is-an-equivalence-because (create-equivalence-proof id id (λ _ → refl) (λ _ → refl))
  
equivalenct-depedent-types-have-equivalent-Π :
  ∀ {i} {A : U i} (P Q : A → U i) (e : (x : A) → P x ≃ Q x)
  → Π P ≃ Π Q
equivalenct-depedent-types-have-equivalent-Π {A = A} P Q e =
  let
    open _≃_ renaming (e to equivalence)
    open _is-an-equivalence
    φ : Π P → Π Q
    φ s x = equivalence (e x) (s x)
    ψ : Π Q → Π P
    ψ s x = ((e x) ⁻¹→) (s x)
  in φ is-an-equivalence-because
    (create-equivalence-proof φ ψ
      (λ s → fun-ext (λ (x : A) → η (proof (e x)) (s x)))
      (λ s → fun-ext (λ (x : A) → ε (proof (e x)) (s x))))

equivalences-are-preserved-by-homotopy : 
  ∀ {i} {A B : U i} (f g : A → B)
  → f is-an-equivalence → f ⇒ g
  → g is-an-equivalence
equivalences-are-preserved-by-homotopy f g record { inverse = inverse ; η = η ; ε = ε ; half-adjoint = half-adjoint } ζ =
  create-equivalence-proof g inverse (λ x → ap inverse (ζ x) ⁻¹ • η x) (λ y → ζ (inverse y) ⁻¹ • ε y)
