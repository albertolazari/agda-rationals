{-# OPTIONS --allow-unsolved-metas #-}
open import Natural+ as N using (ℕ⁺; one; succ)
open import Integer as Z using (ℤ; zero; pos; neg; _×_)
open import Option

module Rational where
  data ℚ : Set where
    _/_ : ℤ → ℕ⁺ → ℚ

  num : ℚ → ℤ
  num (a / b) = a

  den : ℚ → ℕ⁺
  den (a / b) = b

  _+_ : ℚ → ℚ → ℚ
  (zero / b)  + x       = x
  (pos a / b) + (c / d) = ((pos a × d) Z.+ (c × d)) / (b N.× d)
  (neg a / b) + (c / d) = ((neg a × d) Z.+ (c × d)) / (b N.× d)

  -_ : ℚ → ℚ
  - (a / b) = (Z.- a) / b

  _-_ : ℚ → ℚ → ℚ
  x - y = x + (- y)

  _·_ : ℚ → ℚ → ℚ
  (a / b) · (c / d) = (a Z.· c) / (b N.× d)

  _^ₙ_ : ℚ → ℕ⁺ → ℚ
  x ^ₙ one    = x
  x ^ₙ succ y = x · (x ^ₙ y)

  _^_ : ℚ → ℤ → Option ℚ
  x           ^ pos y = item (x ^ₙ y)
  (zero  / b) ^ neg y = empty
  (pos a / b) ^ neg y = item ((pos b / a) ^ₙ y)
  (neg a / b) ^ neg y = item ((neg b / a) ^ₙ y)
  (zero  / b) ^ zero  = empty
  (pos a / b) ^ zero  = item (pos one / one)
  (neg a / b) ^ zero  = item (pos one / one)

  _∶_ : ℚ → ℚ → Option ℚ
  x ∶ y with y ^ neg one
  ... | empty    = empty
  ... | item 1/y = item (x · 1/y)

  infix 5 _≈_
  data _≈_ : ℚ → ℚ → Set where
    eq : {x y : ℚ} → x · (pos (den y) / den y) ≈ y · (pos (den x) / den x)

  infix 5 _≡_
  data _≡_ : ℚ → ℚ → Set where
    refl : {x : ℚ} → x ≡ x

  lemma-times-one : (x : ℚ) → x · (pos one / one) ≈ x
  lemma-times-one x = {!!}
