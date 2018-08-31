{-# OPTIONS --without-K #-}

open import UniversesPiSigma

module Equality where

infix 5 _≈_                                         -- \approx
data _≈_ {i} {A : U i} (a : A) : A → U i where  
  refl : a ≈ a

{- 2-cells/homotopies -}
_⇒_ : ∀ {i j} {A : U i} {B : U j} → (f g : A → B) → U (i ⊔ j)
f ⇒ g = (a : _) → f a ≈ g a

{- concatenation of paths -}
infixl 50 _•_ -- \bu
_•_ : ∀ {i} {A : U i} → {x y z : A} → x ≈ y → y ≈ z → x ≈ z
refl • γ = γ

infixl 50 _•⇒_ 
_•⇒_ : ∀ {i j} {A : U i} {B : U j} {f g h : A → B} 
      → f ⇒ g → g ⇒ h → f ⇒ h
η •⇒ ε = λ x → η x • ε x

infix 60 _⁻¹       -- \^-\^1\bu
_⁻¹ : ∀ {i} {A : U i} {x y : A} → x ≈ y → y ≈ x
refl ⁻¹ = refl

infix 60 _⁻¹⇒
_⁻¹⇒ : ∀ {i j} {A : U i} {B : U j} {f g : A → B} → f ⇒ g → g ⇒ f
H ⁻¹⇒ = λ x → H x ⁻¹

ap : ∀ {i j} {A : U i} {B : U j} {x y : A} (f : A → B)
  → x ≈ y → f(x) ≈ f(y)
ap f refl = refl

refl-is-right-neutral : ∀ {i} {A : U i} {x y : A} (γ : x ≈ y) → γ ≈ γ • refl
refl-is-right-neutral refl = refl
  
refl-is-left-neutral : ∀ {i} {A : U i} {x y : A} (γ : x ≈ y) → γ ≈ refl • γ
refl-is-left-neutral refl = refl
    
•-is-associative : ∀ {i} {A : U i} {w x y z : A} (γ : w ≈ x) (γ′ : x ≈ y) (γ″ : y ≈ z) → γ • (γ′ • γ″) ≈ γ • γ′ • γ″
•-is-associative refl refl refl = refl
  
⁻¹-is-right-inversion : ∀ {i} {A : U i} {x y : A}  (γ : x ≈ y) → γ • γ ⁻¹ ≈ refl
⁻¹-is-right-inversion refl = refl
  
⁻¹-is-left-inversion : ∀ {i} {A : U i} {x y : A}  (γ : x ≈ y) → γ ⁻¹ • γ ≈ refl
⁻¹-is-left-inversion refl = refl
  
⁻¹-is-selfinverse : ∀ {i} {A : U i} {x y : A}  (γ : x ≈ y) → (γ ⁻¹) ⁻¹ ≈ γ
⁻¹-is-selfinverse refl = refl

∘-is-associative : ∀ {i} {A B C D : U i} → (f : A → B) → (g : B → C) → (h : C → D) → h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f
∘-is-associative f g h = refl

naturality-of-homotopies : ∀ {A B : U₀} {a a′ : A} (f g : A → B)
                           → (H : f ⇒ g) → (γ : a ≈ a′)
                           → H a • ap g γ ≈ ap f γ • H a′
naturality-of-homotopies f g H refl =
                             refl-is-right-neutral (H _) ⁻¹ • refl-is-left-neutral (H _)

id-has-trivial-application : ∀ {A : U₀} {a a′ : A} 
                             → (γ : a ≈ a′)
                             → ap id γ ≈ γ
id-has-trivial-application refl = refl

{- 
  equational reasoning 
  this can be used to write down proofs in the following style:
  
     (a + b) + -b
   ≈⟨ associativity _ _ _ ⟩
     a + (b + -b)
   ≈⟨ is-right-inverse _ ⟩
     a + 0
   ≈⟨ 0-is-right-neutral _ ⟩ 
     a 
   ≈∎

  (this is a term of type '(a + b) + -b ≈ a')
-}
infix 15 _≈∎    -- \approx\qed
infixr 10 _≈⟨_⟩_    -- \approx\< \>
  
_≈∎ : ∀ {i} {A : U i} (a : A)
       → a ≈ a
a ≈∎ = refl 
  
_≈⟨_⟩_ : ∀ {i} {A : U i} (a : A) {a′ a″ : A}
         → a ≈ a′ → a′ ≈ a″ → a ≈ a″
a ≈⟨ γ ⟩ η = γ • η


postulate
  fun-ext : ∀ {i j} {A : U i} {P : A → U j}
            → {f g : (a : A) → P a}
            → ((a : A) → f(a) ≈ g(a)) → f ≈ g

