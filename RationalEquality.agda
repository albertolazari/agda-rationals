{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Rational as ℚ  using (ℚ; _/_; num; den)
open import Natural+ as ℕ⁺ using (ℕ⁺; one; succ)
open import Integer  as ℤ  using (ℤ; zero; pos; neg; _×_)
open import Option

module RationalEquality where
data _≅_ : ℚ → ℚ → Set where
  eq : {x y : ℚ} → num x × den y ≡ num y × den x → x ≅ y

≡→≅ : {x y : ℚ} → x ≡ y → x ≅ y
≡→≅ refl = eq refl
