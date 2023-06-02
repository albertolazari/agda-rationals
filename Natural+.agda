{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.PropositionalEquality

module Natural+ where
  data ℕ⁺ : Set where
    one  : ℕ⁺
    succ : ℕ⁺ → ℕ⁺

  _+_ : ℕ⁺ → ℕ⁺ → ℕ⁺
  one    + y = succ y
  succ x + y = succ (x + y)

  _×_ : ℕ⁺ → ℕ⁺ → ℕ⁺
  one    × y = y
  succ x × y = y + (x × y)

  lemma-×-one : {x : ℕ⁺} → x × one ≡ x
  lemma-×-one {one}    = refl
  lemma-×-one {succ x} = cong succ lemma-×-one
