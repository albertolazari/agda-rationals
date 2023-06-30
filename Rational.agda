{-# OPTIONS --allow-unsolved-metas #-}

module Rational where

open import Relation.Binary.PropositionalEquality as ≡

open import Natural+ as ℕ⁺ using (ℕ⁺; one; succ)
open import Integer  as ℤ  using (ℤ; zero; pos; neg; _×_)
open import Rational.Base public
open import Rational.Equivalence public

lemma-≈-zero : {x y : ℕ⁺} → zero / x ≈ zero / y
lemma-≈-zero = eq refl

lemma-≈-one : {n : ℕ⁺} → pos n / n ≈ pos one / one
lemma-≈-one = eq (≡.cong pos (≡.sym ℕ⁺.lemma-×-one))

lemma-·-≈-one : {x : ℚ} {n : ℕ⁺} → x · (pos n / n) ≈ x
lemma-·-≈-one {x} {n} = begin
  x · (pos n / n)     ≈⟨ ≡→≈ (lemma-·-commutative x (pos n / n)) ⟩
  (pos n / n) · x     ≈⟨ lemma-·-cong x lemma-≈-one ⟩
  (pos one / one) · x ≈⟨ ≡→≈ (lemma-·-commutative (pos one / one) x) ⟩
  x · (pos one / one) ≈⟨ ≡→≈ lemma-·-one ⟩
  x                   ∎
  where open ≈-Reasoning

lemma-√2-∉-ℚ : {x : ℚ} → x · x ≉ pos (succ one) / one
lemma-√2-∉-ℚ {zero  / b} (eq contradiction) = ℤ.lemma-pos-≢-zero ((b ℕ⁺.× b) ℕ⁺.× succ one) (≡.sym contradiction)
lemma-√2-∉-ℚ {pos a / b} (eq contradiction) = ℕ⁺.lemma-√2-∉-ℕ⁺ a b (ℤ.lemma-pos-injective contradiction)
lemma-√2-∉-ℚ {neg a / b} (eq contradiction) = ℕ⁺.lemma-√2-∉-ℕ⁺ a b (ℤ.lemma-pos-injective contradiction)
