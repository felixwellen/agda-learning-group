{-

 This is a file with some ideas, what you can do:

 Installation hints for Mac: installing agda with Homebrew and using it with Aquamacs worked   

 First: You should know a little bit of emacs, if you don't
 make sure emacs is installed on your system, start it and
 do the tutorial (hit CTRL-h CTRL-t to start it or find it in some menu).

 Second: Make sure agda is installed on your system and the agda-mode for
 emacs is set up.
-}


-- inductive definition of the natural numbers

data nat : Set where
  zero : nat
  suc : nat -> nat

-- some definition
one = suc zero

-- function definition
map-everything-to-zero : nat -> nat
map-everything-to-zero x = zero

-- function definition using pattern matching
another-map : nat -> nat
another-map zero = one
another-map (suc k) = zero
