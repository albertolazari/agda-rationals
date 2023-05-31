{-# OPTIONS --allow-unsolved-metas #-}
open import Natural+ as N using (ℕ⁺; one; succ)

module Integer where
  data ℤ : Set where
    zero : ℤ
    pos  : ℕ⁺ → ℤ
    neg  : ℕ⁺ → ℤ
  
  -_ : ℤ → ℤ
  - zero  = zero
  - pos x = neg x
  - neg x = pos x

  _-ₙ_ : ℕ⁺ → ℕ⁺ → ℤ
  one    -ₙ one    = zero
  one    -ₙ succ y = neg y
  succ x -ₙ one    = pos x
  succ x -ₙ succ y = x -ₙ y

  _+_ : ℤ → ℤ → ℤ
  zero  + y     = y
  pos x + zero  = pos x
  pos x + pos y = pos (x N.+ y)
  pos x + neg y = x -ₙ y
  neg x + zero  = neg x
  neg x + pos y = y -ₙ x
  neg x + neg y = neg (x N.+ y)

  _-_ : ℤ → ℤ → ℤ
  x - y = x + (- y)

  _×_ : ℤ → ℕ⁺ → ℤ
  zero  × y = zero
  pos x × y = pos (x N.× y)
  neg x × y = neg (x N.× y)

  _·_ : ℤ → ℤ → ℤ
  zero  · y = zero
  pos x · y = y × x
  neg x · y = - (y × x)

  GCD : (x y : ℤ) → ℤ
  GCD x y = {!!}
