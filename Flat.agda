{-# OPTIONS --without-K #-}

{-
  Learnt about agda-flat from Ian Orton:
  (also Dan helped somewhere along the way)

  There is a branch of agda called flat, 
  which supports a comonadic modality called flat or ♭

  This file contains some experiments with ♭
  inspired by mike shulmans real-cohesion paper

  Starting with a 'let'-notation I learnd from Ian

  References to Lemmata and Theorems refer to Mike Shulman's Article

  https://arxiv.org/abs/1509.07584

-}


module Flat where
  open import BasicDefinitions

  data ♭ {l :{♭} Level} (A :{♭} U l) : U l where
    _^♭ : (a :{♭} A) → ♭ A

