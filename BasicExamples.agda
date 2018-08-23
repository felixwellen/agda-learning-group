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


 First: You should know a little bit of emacs, if you don't
 make sure emacs is installed on your system, start it and
 do the tutorial (hit CTRL-h CTRL-t to start it or find it in some menu).

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
