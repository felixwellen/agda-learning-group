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

