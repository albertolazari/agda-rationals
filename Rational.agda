{-# OPTIONS --allow-unsolved-metas #-}
open import Natural+
  renaming (_+_ to _+ₙ_)
  renaming (_×_ to _×ₙ_)
open import Integer
  renaming (-_ to -ᵢ_)
  renaming (_+_ to _+ᵢ_)
  renaming (_·_ to _·ᵢ_)

module Rational where
  data ℚ : Set where
    _/_ : ℤ → ℕ⁺ → ℚ

  infix 5 _≡_
  data _≡_ : ℚ → ℚ → Set where
    refl : {x : ℚ} → x ≡ x

  -_ : ℚ → ℚ
  - (a / b) = (-ᵢ a) / b

  _+_ : ℚ → ℚ → ℚ
  (zero / b)  + x       = x
  (pos a / b) + (c / d) = ((pos a × d) +ᵢ (c × d)) / (b ×ₙ d)
  (neg a / b) + (c / d) = ((neg a × d) +ᵢ (c × d)) / (b ×ₙ d)

  _·_ : ℚ → ℚ → ℚ
  (a / b) · (c / d) = (a ·ᵢ c) / (b ×ₙ d)

  _^_ : ℚ → ℤ → ℚ
  -- zero ^ zero is actually undefined
  x ^ zero  = pos one / one
  x ^ pos one = x
  x ^ pos (succ y) = x · (x ^ pos y)
  -- undefined...
  (zero / b) ^ neg y = zero / b
  (pos x / b) ^ neg y = {!!}
  (neg x / b) ^ neg y = {!!}
