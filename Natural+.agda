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

lemma-+-reverse-cong : {x y : ℕ⁺} → (z : ℕ⁺) → x + z ≡ y + z → x ≡ y
lemma-+-reverse-cong z p = {!!}

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

lemma-×-distributive₁ : (x y z : ℕ⁺) → (x + y) × z ≡ (x × z) + (y × z)
lemma-×-distributive₁ x y z = {!!}

lemma-×-distributive₂ : (x y z : ℕ⁺) → x × (y + z) ≡ (x × y) + (x × z)
lemma-×-distributive₂ x y z = begin
  x × (y + z) ≡⟨ lemma-×-commutative x (y + z) ⟩
  (y + z) × x ≡⟨ lemma-×-distributive₁ y z x ⟩
  (y × x) + (z × x) ≡⟨ cong (_+ (z × x)) (lemma-×-commutative y x) ⟩
  (x × y) + (z × x) ≡⟨ cong ((x × y) +_) (lemma-×-commutative z x) ⟩
  (x × y) + (x × z) ∎

lemma-×-associative : (x y z : ℕ⁺) → (x × y) × z ≡ x × (y × z)
lemma-×-associative one one      z = refl
lemma-×-associative one (succ y) z = refl
lemma-×-associative (succ x) one z = cong (z +_) (cong (_× z) (begin
    x × one   ≡⟨ lemma-×-one ⟩
    x         ∎
  ))
lemma-×-associative (succ x) (succ y) one = cong succ (begin
    (y + (x × succ y)) × one         ≡⟨ lemma-×-one ⟩
    y + (x × succ y)                 ≡⟨ cong (y +_) (cong (x ×_) (cong succ (sym lemma-×-one))) ⟩
    y + (x × succ (y × one))         ≡⟨ cong (_+ (x × succ (y × one))) (sym lemma-×-one) ⟩
    (y × one) + (x × succ (y × one)) ∎
  )
lemma-×-associative (succ x) (succ y) (succ z) = cong succ (begin
  z + ((y + (x × succ y)) × succ z) ≡⟨ cong (z +_) (begin
    (y + (x × succ y)) × succ z                     ≡⟨ cong (_× succ z) (cong (y +_) (lemma-×-commutative x (succ y))) ⟩
    (y + (x + (y × x))) × succ z                    ≡⟨ lemma-×-commutative (y + (x + (y × x))) (succ z) ⟩
    succ z × (y + (x + (y × x)))                    ≡⟨⟩
    (y + (x + (y × x))) + (z × (y + (x + (y × x)))) ≡⟨ lemma-+-associative y (x + (y × x)) (z × (y + (x + (y × x)))) ⟩
    y + ((x + (y × x)) + (z × (y + (x + (y × x))))) ≡⟨ cong (y +_) (begin
      (x + (y × x)) + (z × (y + (x + (y × x)))) ≡⟨ lemma-+-associative x (y × x) (z × (y + (x + (y × x)))) ⟩
      x + ((y × x) + (z × (y + (x + (y × x))))) ≡⟨ cong (x +_) (begin
        (y × x) + (z × (y + (x + (y × x)))) ≡⟨ cong ((y × x) +_) (begin
          z × (y + (x + (y × x)))             ≡⟨ lemma-×-distributive₂ z y (x + (y × x)) ⟩
          (z × y) + (z × (x + (y × x)))       ≡⟨ lemma-+-commutative ((z × y)) (z × (x + (y × x))) ⟩
          (z × (x + (y × x))) + (z × y)       ≡⟨ cong (_+ (z × y)) (lemma-×-distributive₂ z x (y × x)) ⟩
          ((z × x) + (z × (y × x))) + (z × y) ≡⟨ cong (_+ (z × y)) (cong ((z × x) +_) (sym (lemma-×-associative z y x))) ⟩
          ((z × x) + ((z × y) × x)) + (z × y) ∎
        ) ⟩
        (y × x) + (((z × x) + ((z × y) × x)) + (z × y)) ≡⟨ sym (lemma-+-associative (y × x) ((z × x) + ((z × y) × x)) (z × y)) ⟩
        ((y × x) + ((z × x) + ((z × y) × x))) + (z × y) ≡⟨ cong (_+ (z × y)) (begin
          (y × x) + ((z × x) + ((z × y) × x)) ≡⟨ sym (lemma-+-associative (y × x) (z × x) ((z × y) × x)) ⟩
          ((y × x) + (z × x)) + ((z × y) × x) ≡⟨ cong (_+ ((z × y) × x)) (sym (lemma-×-distributive₁ y z x)) ⟩
          ((y + z) × x) + ((z × y) × x)       ≡⟨ sym (lemma-×-distributive₁ (y + z) (z × y) x) ⟩
          ((y + z) + (z × y)) × x             ≡⟨ cong (_× x) (cong (_+ (z × y)) (lemma-+-commutative y z)) ⟩
          ((z + y) + (z × y)) × x             ≡⟨ cong (_× x) (lemma-+-associative z y (z × y)) ⟩
          (z + (y + (z × y))) × x             ∎
        ) ⟩
        ((z + (y + (z × y))) × x) + (z × y) ∎
      ) ⟩
      x + (((z + (y + (z × y))) × x) + (z × y)) ≡⟨ sym (lemma-+-associative x ((z + (y + (z × y))) × x) (z × y)) ⟩
      (x + ((z + (y + (z × y))) × x)) + (z × y) ≡⟨ lemma-+-commutative (x + ((z + (y + (z × y))) × x)) (z × y) ⟩
      (z × y) + (x + ((z + (y + (z × y))) × x)) ∎
    ) ⟩
    y + ((z × y) + (x + ((z + (y + (z × y))) × x))) ≡⟨ sym (lemma-+-associative y (z × y) (x + ((z + (y + (z × y))) × x))) ⟩
    (y + (z × y)) + (x + ((z + (y + (z × y))) × x)) ∎
  ) ⟩
  z + ((y + (z × y)) + (x + ((z + (y + (z × y))) × x))) ≡⟨ sym (lemma-+-associative z (y + (z × y)) (x + ((z + (y + (z × y))) × x))) ⟩
  (z + (y + (z × y))) + (x + ((z + (y + (z × y))) × x)) ≡⟨⟩
  (z + (y + (z × y))) + (succ (z + (y + (z × y))) × x)  ≡⟨ cong ((z + (y + (z × y))) +_) (lemma-×-commutative (succ (z + (y + (z × y)))) x) ⟩
  (z + (y + (z × y))) + (x × succ (z + (y + (z × y))))  ≡⟨⟩
  (z + (y + (z × y))) + (x × succ (z + (succ z × y)))   ≡⟨ cong ((z + (y + (z × y))) +_) (cong (x ×_) (cong succ (cong (z +_) (lemma-×-commutative (succ z) y)))) ⟩
  (z + (y + (z × y))) + (x × succ (z + (y × succ z)))   ≡⟨⟩
  (z + (succ z × y)) + (x × succ (z + (y × succ z)))    ≡⟨ cong (_+ (x × succ (z + (y × succ z)))) (cong (z +_) (lemma-×-commutative (succ z) y)) ⟩
  (z + (y × succ z)) + (x × succ (z + (y × succ z)))    ∎
  )

lemma-×-reverse-cong₁ : {x y : ℕ⁺} → (z : ℕ⁺)
  → x × z ≡ y × z
  → x ≡ y
lemma-×-reverse-cong₁ {x} {y} one p = begin
  x       ≡⟨ sym lemma-×-one ⟩
  x × one ≡⟨ p ⟩
  y × one ≡⟨ lemma-×-one ⟩
  y ∎
lemma-×-reverse-cong₁ {x} {y} (succ z) p = {!!}
  where
  aux-×-commutative : {x y : ℕ⁺} → (z : ℕ⁺)
    → x × z ≡ y × z
    → z × x ≡ z × y
  aux-×-commutative {x} {y} z p = begin
    z × x ≡⟨ lemma-×-commutative z x ⟩
    x × z ≡⟨ p ⟩
    y × z ≡⟨ lemma-×-commutative y z ⟩
    z × y ∎

  aux-+-commutative : {x y : ℕ⁺} → (z : ℕ⁺)
    → z + x ≡ z + y
    → x + z ≡ y + z
  aux-+-commutative z p = {!!}

lemma-×-reverse-cong₂ : {x y : ℕ⁺} → (z : ℕ⁺) → z × x ≡ z × y → x ≡ y
lemma-×-reverse-cong₂ {x} {y} z p = lemma-×-reverse-cong₁ z (aux-commutative z p)
  where
  aux-commutative : {x y : ℕ⁺} → (z : ℕ⁺)
    → z × x ≡ z × y
    → x × z ≡ y × z
  aux-commutative {x} {y} z p = begin
    x × z ≡⟨ lemma-×-commutative x z ⟩
    z × x ≡⟨ p ⟩
    z × y ≡⟨ lemma-×-commutative z y ⟩
    y × z ∎
