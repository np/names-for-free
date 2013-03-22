{-# OPTIONS --no-positivity-check #-}
module nbe-terms where

data Neu A : Set
data Sem A : Set

data Neu A where
  V   : A → Neu A
  _·_ : Neu A → Sem A → Neu A

data Sem A where
  ƛ : (Sem A → Sem A) → Sem A
  N : Neu A → Sem A
