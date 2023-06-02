{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

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
  (a / b) + (c / d) = ((a × d) Z.+ (c × b)) / (b N.× d)

  lemma-+-zero : {x : ℚ} → (zero / one) + x ≡ x
  lemma-+-zero {a / b} = begin
    (zero / one) + (a / b)                   ≡⟨⟩
    ((zero × b) Z.+ (a × one)) / (one N.× b) ≡⟨⟩
    (zero       Z.+ (a × one)) / b           ≡⟨⟩
                    (a × one)  / b           ≡⟨ {!!} ⟩
                    a          / b           ∎

  lemma-+-commutative : (x y : ℚ) → x + y ≡ y + x
  lemma-+-commutative x y = {!!}

  -_ : ℚ → ℚ
  - (a / b) = (Z.- a) / b

  _-_ : ℚ → ℚ → ℚ
  x - y = x + (- y)

  lemma-negation : {x : ℚ} → (zero / one) - x ≡ - x
  lemma-negation = {!!}

  lemma-sub-zero : {x : ℚ} → x - (zero / one) ≡ x
  lemma-sub-zero = {!!}

  _·_ : ℚ → ℚ → ℚ
  (a / b) · (c / d) = (a Z.· c) / (b N.× d)

  lemma-times-one : {x : ℚ} → x · (pos one / one) ≡ x
  lemma-times-one = {!!}

  lemma-times-commutative : {x y : ℚ} → x · y ≡ y · x
  lemma-times-commutative = {!!}

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
