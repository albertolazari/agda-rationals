{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Maybe

open import Natural+ as ℕ⁺ using (ℕ⁺; one; succ)
open import Integer  as ℤ  using (ℤ; zero; pos; neg; _×_)

module Rational where
data ℚ : Set where
  _/_ : ℤ → ℕ⁺ → ℚ

num : ℚ → ℤ
num (a / b) = a

den : ℚ → ℕ⁺
den (a / b) = b 

ℤ-den : ℚ → ℤ
ℤ-den (a / b) = pos b 

transport-on-num : {x y : ℤ} {b : ℕ⁺} → x ≡ y → x / b ≡ y / b
transport-on-num refl = refl

transport-on-den : {x y : ℕ⁺} {a : ℤ} → x ≡ y → a / x ≡ a / y
transport-on-den refl = refl

_+_ : ℚ → ℚ → ℚ
(a / b) + (c / d) = ((a × d) ℤ.+ (c × b)) / (b ℕ⁺.× d)

lemma-+-commutative : (x y : ℚ) → x + y ≡ y + x
lemma-+-commutative (a / b) (c / d) = begin
  ((a × d) ℤ.+ (c × b)) / (b ℕ⁺.× d) ≡⟨ transport-on-num (ℤ.lemma-+-commutative (a × d) (c × b)) ⟩
  ((c × b) ℤ.+ (a × d)) / (b ℕ⁺.× d) ≡⟨ transport-on-den (ℕ⁺.lemma-×-commutative b d) ⟩
  ((c × b) ℤ.+ (a × d)) / (d ℕ⁺.× b) ∎

lemma-+-zero₁ : {x : ℚ} → (zero / one) + x ≡ x
lemma-+-zero₁ {a / b} = begin
  (zero / one) + (a / b)                    ≡⟨⟩
  ((zero × b) ℤ.+ (a × one)) / (one ℕ⁺.× b) ≡⟨⟩
  (zero       ℤ.+ (a × one)) / b            ≡⟨⟩
                  (a × one)  / b            ≡⟨ transport-on-num ℤ.lemma-×-one ⟩
                           a / b            ∎

lemma-+-zero₂ : {x : ℚ} →  x + (zero / one) ≡ x
lemma-+-zero₂ {x} = begin
  x + (zero / one) ≡⟨ lemma-+-commutative x (zero / one) ⟩
  (zero / one) + x ≡⟨ lemma-+-zero₁ ⟩
  x                ∎

-_ : ℚ → ℚ
- (a / b) = (ℤ.- a) / b

_-_ : ℚ → ℚ → ℚ
x - y = x + (- y)

lemma-negation : {x : ℚ} → (zero / one) - x ≡ - x
lemma-negation {x} = begin
  (zero / one) - x     ≡⟨⟩
  (zero / one) + (- x) ≡⟨ lemma-+-zero₁ ⟩
  - x                  ∎

lemma-sub-zero : {x : ℚ} → x - (zero / one) ≡ x
lemma-sub-zero {x} = begin
  x - (zero / one)     ≡⟨⟩
  x + (- (zero / one)) ≡⟨ lemma-+-zero₂ ⟩
  x                    ∎

_·_ : ℚ → ℚ → ℚ
(a / b) · (c / d) = (a ℤ.· c) / (b ℕ⁺.× d)

lemma-·-one : {x : ℚ} → x · (pos one / one) ≡ x
lemma-·-one {a / b} = begin
  (a / b) · (pos one / one)      ≡⟨⟩
  (a ℤ.· pos one) / (b ℕ⁺.× one) ≡⟨ transport-on-num ℤ.lemma-·-one ⟩
  a / (b ℕ⁺.× one)               ≡⟨ transport-on-den ℕ⁺.lemma-×-one ⟩
  a / b                          ∎

lemma-·-commutative : (x y : ℚ) → x · y ≡ y · x
lemma-·-commutative (a / b) (c / d) = begin
  (a / b) · (c / d)      ≡⟨⟩
  (a ℤ.· c) / (b ℕ⁺.× d) ≡⟨ transport-on-num (ℤ.lemma-·-commutative a c) ⟩
  (c ℤ.· a) / (b ℕ⁺.× d) ≡⟨ transport-on-den (ℕ⁺.lemma-×-commutative b d) ⟩
  (c ℤ.· a) / (d ℕ⁺.× b) ≡⟨⟩
  (c / d) · (a / b)      ∎

_^ₙ_ : ℚ → ℕ⁺ → ℚ
x ^ₙ one    = x
x ^ₙ succ y = x · (x ^ₙ y)

_^_ : ℚ → ℤ → Maybe ℚ
x           ^ pos y = just (x ^ₙ y)
(zero  / b) ^ neg y = nothing
(pos a / b) ^ neg y = just ((pos b / a) ^ₙ y)
(neg a / b) ^ neg y = just ((neg b / a) ^ₙ y)
(zero  / b) ^ zero  = nothing
(pos a / b) ^ zero  = just (pos one / one)
(neg a / b) ^ zero  = just (pos one / one)

_∶_ : ℚ → ℚ → Maybe ℚ
x ∶ y with y ^ neg one
... | nothing    = nothing
... | just 1/y = just (x · 1/y)
