{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module Natural+ where
  data ℕ⁺ : Set where
    one  : ℕ⁺
    succ : ℕ⁺ → ℕ⁺

  _+_ : ℕ⁺ → ℕ⁺ → ℕ⁺
  one    + y = succ y
  succ x + y = succ (x + y)

  lemma-+-one : {x : ℕ⁺} → succ x ≡ x + one
  lemma-+-one {x} = {!!}

  lemma-+-commutative : (x y : ℕ⁺) → x + y ≡ y + x
  lemma-+-commutative one      y = lemma-+-one
  lemma-+-commutative (succ x) y = {!!}

  _×_ : ℕ⁺ → ℕ⁺ → ℕ⁺
  one    × y = y
  succ x × y = y + (x × y)

  lemma-×-one : {x : ℕ⁺} → x × one ≡ x
  lemma-×-one {one}    = refl
  lemma-×-one {succ x} = cong succ lemma-×-one
