{-

 This is a file with some ideas, what you can do:
 
 Install agda and emacs.

 Installation hints for Mac: 
  installing agda with Homebrew and using it with Aquamacs worked   
  if the agda-mode in Aquamacs doesn't work, you can try to remove the compiled mode files
  you can find the directory containing them with
  
  agda-mode locata

  go to the directory and do

  rm *.elc


 Maybe First: You should know a little bit of emacs, if you don't,
 make sure emacs is installed on your system, start it and
 do the tutorial (hit CTRL-h CTRL-t to start it or find it in some menu).

 Make a test.agda file in Aquamacs and write copy paste this file into it
 and try to 'load' it with CTRL-c CTRL-l.
 If everything works like it should, the text should become colored.
 (Here is a list of some commands in the emacs mode:
 https://agda.readthedocs.io/en/v2.5.2/tools/emacs-mode.html
 - but most of them just start to make sense later.)
-}

-- one line comments start with '--'

-- inductive definition of the natural numbers

data nat : Set where
  zero : nat
  suc : nat -> nat

-- some definition
one = suc zero    -- the '=' means something like ':≡' in HoTT


-- function definition
map-everything-to-zero : nat -> nat
map-everything-to-zero x = zero

-- function definition using pattern matching
another-map : nat -> nat
another-map zero = one
another-map (suc k) = zero

{-  (<- this starts a comment..)

  things you could try now:
  define a function double, which doubles its argument
  define a function +

  You can normalize (evaluate) a term with CTRL-c CTRL-n, to see if
  double(one)
  gives the correct

-}  -- ( <- this ends a comment)

{-
 here is another inductive type
 which uses a type parameter --
 the type of lists of terms of type A
-}

data list (A : Set) : Set where
     empty : list A
     cons : A -> list A -> list A

-- here is an example function
append : list nat -> list nat -> list nat
append empty l2 = l2
append (cons x l1) l2 = cons x (append l1 l2)

{-
  There is a feature of agda called 'hole'.
  You can make a hole in an incomplete definition, 
  for example, you could have started to define 'append' by writing:

    append : list nat -> list nat -> list nat
    append l1 l2 = ?

  If you press CTRL-c CTRL-l now, agda will create a 'hole' where the '?' was.
  You can now write something into the hole and interact with agda.
  For example, write 'l1' into the hole and hit CTRL-c CTRL-c
  to let agda make a case distinction on l1. Then it should look like this:

    append : list nat -> list nat -> list nat
    append empty l2 = {!!}
    append (cons x l1) l2 = {!!}

  You have two holes now! Try to write the correct term into them and ask agda
  to fill them by hitting CTRL-c CTRL-r.
-}

{-
  things you can do now:
  define a function adding all numbers in a list
  define a length function from lists of natural numbers to natural numbers
-}

{-
  we will now define products of types 
-}

data product (A : Set) (B : Set) : Set where
  pair : A -> B -> product A B

-- using parameters 'A' and 'B' in function definitions works like follows:

swap' : (A : Set) (B : Set) -> product A B -> product B A
swap' A B (pair a b) = pair b a

-- we can ask agda to figure out 'A' and 'B' on its own wiht curly braces

swap : {A : Set} {B : Set} -> product A B -> product B A
swap (pair a b) = pair b a

{-
  Exercises:
  write curry and uncurry functions
  write a function 'reverse' which reverses a list 
-}

{-
  Let's introduce some fancy notation.
  We can use '_' to tell agda, where the arguments in a definition go.
  Let's use this to get a nicer syntax for the plus function:
-}

_+_ : nat -> nat -> nat
zero    + l = l
(suc k) + l = suc (k + l)

-- and for products:

data _x_ (A : Set) (B : Set) : Set where
  _,_ : A -> B -> A x B

{- projections -}
x-p1 : {A B : Set} → A x B → A
x-p1 (a , b) = a

x-p2 : {A B : Set} → A x B → B
x-p2 (a , b) = b

{-
  write a function 'reverse' which reverses a list.
-}

{-
  In the emacs mode for agda, you can also enter some unicode symbols 
  and use them as identifiers. Here are some examples:
    type         to get
    \bN           ℕ
    \bZ           ℤ
    \times        ×
    \Pi           Π
    \Sigma        Σ
  To see a full list you can hit ALT-x and enter 'describe-input-method'.
  In some cases, you end up at a list of symbols from which you can chose 
  with the arrow keys. Try '\bu' and '\r'.

  So here are the naturals again:
-}

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{- 
  note that we also replaced '->' with '→', where the latter is the first 
  option of '\r'.

  Let us continue with (preliminary versions of) dependent sums and products.
  For a dependent type 'P : A → Set', the product is denoted '(x : A) → P x'
  in agda. We can still introduce a 'Π':
-}

Π : (A : Set) → (P : A → Set) → Set
Π A P = (x : A) → P x

{-
  For 'data'-types with just one constructor, agda has 'record'-types, which
  have some additional features. We use those for dependent sums:
-}

record Σ (A : Set) (P : A → Set) : Set where
  constructor _,_
  field
    a : A
    p : P a
    
{-
  projections, defined by pattern matching:
-}

p1 : (A : Set) → (P : A → Set) → Σ A P → A
p1 A P (a , p) = a

{- 
  We can have agda figure out the first two arguments in most cases:
  (and use a unicode-name '\pi\_1')
-}

π₁ : {A : Set} → {P : A → Set} → Σ A P → A
π₁ (a , p) = a

{-
  define the second projection!
  you can also try to write a dependent (un-)curry-function
-}


{-
  equality is also defined using 'data'
  we use '\approx' as our symbol for equality
  it is also accessible via '\eq' (go through the options with using arrow keys)
-}

data _≈_ {A : Set} (x : A) : A → Set where
  refl : x ≈ x

{- 
  we could also arrange the parameters like this:

  data _≈_ {A : Set} (x : A) (y : A) : Set where

  but what we did is known to work well...
-}

{-
  here is one basic example:
-}

ap : {A B : Set} {x y : A} (f : A → B) → (x ≈ y) → (f(x) ≈ f(y))
ap f refl = refl

{-
  try to define:
  * concatenation of equalities (transitivity)
  * inversion/symmetry
  * associativity
  * ...
  if you are stuck, look at 'Equality.agda' in the git-repo of the learning group

  Then try to show: 
  * 'zero' (in ℕ) is right-neutral
  * reversing a list preserves its length (this is some work...)
  * reversing a list twice, is the list you started with (this is some work...)
-}


{- 

solutions: 

  |
  v



-}



length : list nat → nat
length empty = zero
length (cons x l) = suc (length l) 

reverse' : list nat → list nat → (list nat) x (list nat)
reverse' empty  l2 = empty , l2
reverse' (cons y l1)  l2 = reverse' l1 (cons y l2)

reverse : list nat → list nat
reverse l = x-p2 (reverse' l empty)

curry : {A : Set} {B : Set} {C : Set}
      -> ((A x B) -> C) -> (A -> B -> C)
curry f a b = f (a , b)

concatenate : {A : Set} {x y z : A}
  → x ≈ y → y ≈ z → x ≈ z
concatenate refl refl = refl

commute-one :
  (n m : nat)
  → (suc (n + m)) ≈ (n + (suc m))
commute-one zero m = refl
commute-one (suc n) m = ap suc (commute-one n m)

lemma-length-suc : (l k : list nat) (n : nat)
  → suc (length (x-p2 (reverse' l k))) ≈ length (x-p2 (reverse' l (cons n k)))
lemma-length-suc empty k n = refl
lemma-length-suc (cons x l) k n = {!!}

lemma-length-reverse : (l k : list nat)
  → ((length l) + (length k))
    ≈ length (x-p2 (reverse' l k))
lemma-length-reverse empty l = refl
lemma-length-reverse (cons y l') k =
  concatenate (ap suc (lemma-length-reverse l' k)) {!!}


reverse-preserves-length :
  (l : list nat)
  → length l ≈ length (reverse l)
reverse-preserves-length empty = refl
reverse-preserves-length (cons x l) = {!!}

{-
      length : list A → ℕ
    length [] = zero
    length (x ∷ l) = (length l) +1

    length-is-homomorphic :
      ∀ (l k : list A)
      → length (l ++ k) ≈ (length l) + (length k)
    length-is-homomorphic [] k = refl
    length-is-homomorphic (x ∷ l) k =
        length ((x ∷ l) ++ k)
      ≈⟨ (λ z → z +1) ⁎ (length-is-homomorphic l k) ⟩
       (length l + length k) +1
      ≈⟨ commute-1 (length l) _ ⟩
        (length l +1) + length k
      ≈⟨ refl ⟩
        length (x ∷ l) + length k
      ≈∎

    private
      reverse' : list A → list A → (list A × list A)
      reverse' []  k = ([] , k)
      reverse' (x ∷ l) k = reverse' l (x ∷ k)

      length-invariance :
        ∀ (l k : list A)
        → length l + length k ≈ length (π₂ (reverse' l k))
      length-invariance [] k = refl
      length-invariance (x ∷ l) k = length-invariance l (x ∷ k)


    reverse : list A → list A
    reverse l = π₂ (reverse' l [])

    length-invariance-of-reverse :
      ∀ (l : list A)
      → length l ≈ length (reverse l)
    length-invariance-of-reverse l =
                                 length l
                               ≈⟨ zero-is-right-neutral _ ⁻¹ ⟩
                                 length l + length []
                               ≈⟨ length-invariance l [] ⟩
                                 length (π₂ (reverse' l []))
                               ≈⟨ refl ⟩
                                 length (reverse l)
                               ≈∎



-}
