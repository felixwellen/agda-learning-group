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


 Maybe First: You should know a little bit of emacs, if you don't
 make sure emacs is installed on your system, start it and
 do the tutorial (hit CTRL-h CTRL-t to start it or find it in some menu).

 Make a test.agda file in Aquamacs and write copy paste this file into it
 and try to 'load' it with CTRL-c CTRL-l.
 If everything works like it should, the text should become colored.
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

-}  (<- this ends a comment)

