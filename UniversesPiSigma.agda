{-# OPTIONS --without-K #-}

module UniversesPiSigma where
{-
  First, rename 'Set' to 'U', since we are interested in
  HoTT. Also introduce Universe-Levels
-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

U : (i : Level) → Set (lsuc i)
U i = Set i

U₀ = U lzero
U₁ = U (lsuc lzero)


{-
  dependent product...
-}

Π : ∀ {i j} → {A : U i} → (P : A → U j) → U (i ⊔ j)
Π {A = A} P = (a : A) → P a

{-
  dependent sum...
-}

record Σ {i j} {A : U i} (P : A → U j) : U (i ⊔ j) where
  constructor _,_
  field
    a : A
    p : P a

Σπ₁ : ∀ {i} {j} {A : U i} {P : A → U j} 
  → Σ P → A
Σπ₁ (a , _) = a

Σπ₂ : ∀ {i} {j} {A : U i} {P : A → U j}
  → (x : Σ P) → P (Σπ₁ x)
Σπ₂ (a , p) = p  

_×_ : 
  ∀ {i j} 
  → (A : U i) → (B : U j) → U (i ⊔ j)
A × B = Σ (λ (a : A) → B)


π₁ : ∀ {i} {A : U i} {B : U i} → A × B → A
π₁ (a , b) = a

π₂ : ∀ {i} {A : U i} {B : U i} → A × B → B
π₂ (a , b) = b 

{- this extends × to functions -}

_×→_ : ∀ {A B A′ B′ : U₀} → (A → B) → (A′ → B′) → (A × A′ → B × B′)
f ×→ g = λ { (a , b) → f a , g b }


id : ∀ {i} {A : U i} → A → A
id a = a

identity-on : (A : U₀) → A → A
identity-on A = (λ (x : A) → x)

infixr 70 _∘_
_∘_ : ∀ {i j k} {A : U i} {B : U j} {C : U k} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g(f(x))
