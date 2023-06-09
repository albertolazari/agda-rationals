{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Natural+ as ℕ⁺ using (ℕ⁺; one; succ)

module Integer where
data ℤ : Set where
  zero : ℤ
  pos  : ℕ⁺ → ℤ
  neg  : ℕ⁺ → ℤ

data ℤ₀ : ℤ → Set where
  pos₀ : {x : ℕ⁺} → ℤ₀ (pos x)
  neg₀ : {x : ℕ⁺} → ℤ₀ (neg x)

lemma-pos-injective : {x y : ℕ⁺} → pos x ≡ pos y → x ≡ y
lemma-pos-injective {one}    {one}    p    = refl
lemma-pos-injective {succ x} {succ y} refl = refl

lemma-neg-injective : {x y : ℕ⁺} → neg x ≡ neg y → x ≡ y
lemma-neg-injective {one}    {one}    p    = refl
lemma-neg-injective {succ x} {succ y} refl = refl

lemma-injective : {x y : ℤ} → (x₀ : ℤ₀ x) → (y₀ : ℤ₀ y) → x₀ ≡ y₀ → x ≡ y
lemma-injective {x} {y} p = {!!}

-_ : ℤ → ℤ
- zero  = zero
- pos x = neg x
- neg x = pos x

_-ₙ_ : ℕ⁺ → ℕ⁺ → ℤ
one    -ₙ one    = zero
one    -ₙ succ y = neg y
succ x -ₙ one    = pos x
succ x -ₙ succ y = x -ₙ y

_+_ : ℤ → ℤ → ℤ
zero  + y     = y
pos x + zero  = pos x
pos x + pos y = pos (x ℕ⁺.+ y)
pos x + neg y = x -ₙ y
neg x + zero  = neg x
neg x + pos y = y -ₙ x
neg x + neg y = neg (x ℕ⁺.+ y)

lemma-+-zero : {x : ℤ} → x + zero ≡ x
lemma-+-zero {zero}  = refl
lemma-+-zero {pos x} = refl
lemma-+-zero {neg x} = refl

lemma-+-commutative : (x y : ℤ) → x + y ≡ y + x
lemma-+-commutative zero    y       = sym lemma-+-zero
lemma-+-commutative (pos x) zero    = refl
lemma-+-commutative (pos x) (pos y) = cong pos (ℕ⁺.lemma-+-commutative x y)
lemma-+-commutative (pos x) (neg y) = refl
lemma-+-commutative (neg x) zero    = refl
lemma-+-commutative (neg x) (pos y) = refl
lemma-+-commutative (neg x) (neg y) = cong neg (ℕ⁺.lemma-+-commutative x y)

_-_ : ℤ → ℤ → ℤ
x - y = x + (- y)

_×_ : ℤ → ℕ⁺ → ℤ
zero  × y = zero
pos x × y = pos (x ℕ⁺.× y)
neg x × y = neg (x ℕ⁺.× y)

lemma-×-one : {x : ℤ} → x × one ≡ x
lemma-×-one {zero}  = refl
lemma-×-one {pos x} = cong pos ℕ⁺.lemma-×-one
lemma-×-one {neg x} = cong neg ℕ⁺.lemma-×-one

lemma-×-injective : {x y : ℤ} → (z : ℕ⁺) → x × z ≡ y × z → x ≡ y
lemma-×-injective {zero}  {zero}  z p = refl
lemma-×-injective {pos x} {pos y} z p = cong pos (ℕ⁺.lemma-×-injective₁ z (lemma-pos-injective p))
lemma-×-injective {neg x} {neg y} z p = cong neg (ℕ⁺.lemma-×-injective₁ z (lemma-neg-injective p))

_·_ : ℤ → ℤ → ℤ
zero  · y = zero
pos x · y = y × x
neg x · y = - (y × x)

lemma-·-zero : {x : ℤ} → x · zero ≡ zero
lemma-·-zero {zero}  = refl
lemma-·-zero {pos x} = refl
lemma-·-zero {neg x} = refl

lemma-·-one : {x : ℤ} → x · pos one ≡ x
lemma-·-one {zero}  = refl
lemma-·-one {pos x} = refl
lemma-·-one {neg x} = refl

lemma-·-commutative : (x y : ℤ) → x · y ≡ y · x
lemma-·-commutative zero    y       = sym (lemma-·-zero {y})
lemma-·-commutative (pos x) zero    = refl
lemma-·-commutative (pos x) (pos y) = cong pos (ℕ⁺.lemma-×-commutative y x)
lemma-·-commutative (pos x) (neg y) = cong neg (ℕ⁺.lemma-×-commutative y x)
lemma-·-commutative (neg x) zero    = refl
lemma-·-commutative (neg x) (pos y) = cong neg (ℕ⁺.lemma-×-commutative y x)
lemma-·-commutative (neg x) (neg y) = cong pos (ℕ⁺.lemma-×-commutative y x)

lemma-·-associative : (x y z : ℤ) → (x · y) · z ≡ x · (y · z)
lemma-·-associative zero    y       z       = refl
lemma-·-associative (pos x) zero    z       = refl
lemma-·-associative (pos x) (pos y) zero    = refl
lemma-·-associative (pos x) (pos y) (pos z) = cong pos (sym (ℕ⁺.lemma-×-associative z y x))
lemma-·-associative (pos x) (pos y) (neg z) = cong neg (sym (ℕ⁺.lemma-×-associative z y x))
lemma-·-associative (pos x) (neg y) zero    = refl
lemma-·-associative (pos x) (neg y) (pos z) = cong neg (sym (ℕ⁺.lemma-×-associative z y x))
lemma-·-associative (pos x) (neg y) (neg z) = cong pos (sym (ℕ⁺.lemma-×-associative z y x))
lemma-·-associative (neg x) zero    z       = refl
lemma-·-associative (neg x) (pos y) zero    = refl
lemma-·-associative (neg x) (pos y) (pos z) = cong neg (sym (ℕ⁺.lemma-×-associative z y x))
lemma-·-associative (neg x) (pos y) (neg z) = cong pos (sym (ℕ⁺.lemma-×-associative z y x))
lemma-·-associative (neg x) (neg y) zero    = refl
lemma-·-associative (neg x) (neg y) (pos z) = cong pos (sym (ℕ⁺.lemma-×-associative z y x))
lemma-·-associative (neg x) (neg y) (neg z) = cong neg (sym (ℕ⁺.lemma-×-associative z y x))
