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
lemma-+-one {one}    = refl
lemma-+-one {succ x} = cong succ lemma-+-one

lemma-+-associative : (x y z : ℕ⁺) → (x + y) + z ≡ x + (y + z)
lemma-+-associative one      y z = refl
lemma-+-associative (succ x) y z = cong succ (lemma-+-associative x y z)

lemma-+-commutative : (x y : ℕ⁺) → x + y ≡ y + x
lemma-+-commutative one      y = lemma-+-one
lemma-+-commutative (succ x) y = begin
  succ x + y    ≡⟨⟩
  succ (x + y)  ≡⟨ cong succ (lemma-+-commutative x y) ⟩
  succ (y + x)  ≡⟨ lemma-+-one ⟩
  (y + x) + one ≡⟨ lemma-+-associative y x one ⟩
  y + (x + one) ≡⟨ cong (y +_) (sym lemma-+-one) ⟩
  y + succ x    ∎

_×_ : ℕ⁺ → ℕ⁺ → ℕ⁺
one    × y = y
succ x × y = y + (x × y)

lemma-×-one : {x : ℕ⁺} → x × one ≡ x
lemma-×-one {one}    = refl
lemma-×-one {succ x} = cong succ lemma-×-one

lemma-×-commutative : (x y : ℕ⁺) → x × y ≡ y × x
lemma-×-commutative one      y        = sym lemma-×-one
lemma-×-commutative (succ x) one      = lemma-×-one
lemma-×-commutative (succ x) (succ y) =
  let lemma-+-comm-ass : (x y z : ℕ⁺) → x + (y + z) ≡ y + (x + z)
      lemma-+-comm-ass x y z = begin
        x + (y + z) ≡⟨ sym (lemma-+-associative x y z) ⟩
        (x + y) + z ≡⟨ cong (_+ z) (lemma-+-commutative x y) ⟩
        (y + x) + z ≡⟨ lemma-+-associative y x z ⟩
        y + (x + z) ∎
  in
    begin
    succ x × succ y          ≡⟨⟩
    succ (y + (x × succ y))  ≡⟨ cong succ (cong (y +_) (lemma-×-commutative x (succ y)))  ⟩
    succ (y + (succ y × x))  ≡⟨⟩
    succ (y + (x + (y × x))) ≡⟨ cong succ (lemma-+-comm-ass y x (y × x)) ⟩
    succ (x + (y + (y × x))) ≡⟨ cong succ (cong (x +_) (cong (y +_) (lemma-×-commutative y x))) ⟩
    succ (x + (y + (x × y))) ≡⟨⟩
    succ x + (succ x × y)    ≡⟨ cong succ (cong (x +_) (lemma-×-commutative (succ x) y)) ⟩
    succ x + (y × succ x)    ≡⟨⟩
    succ y × succ x          ∎
