{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Natural+ as ℕ⁺ using (ℕ⁺; one; succ)

module Integer where
data ℤ : Set where
  zero : ℤ
  pos  : ℕ⁺ → ℤ
  neg  : ℕ⁺ → ℤ

lemma-pos-reverse-cong : {a b : ℕ⁺} → pos a ≡ pos b → a ≡ b
lemma-pos-reverse-cong {one}    {one}    p    = refl
lemma-pos-reverse-cong {succ a} {succ b} refl = refl

lemma-neg-reverse-cong : {a b : ℕ⁺} → neg a ≡ neg b → a ≡ b
lemma-neg-reverse-cong {one}    {one}    p    = refl
lemma-neg-reverse-cong {succ a} {succ b} refl = refl

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

lemma-×-reverse-cong : {a b : ℤ} → (c : ℕ⁺) → a × c ≡ b × c → a ≡ b
lemma-×-reverse-cong {zero}  {zero}  c p = refl
lemma-×-reverse-cong {pos a} {pos b} c p = cong pos (ℕ⁺.lemma-×-reverse-cong (lemma-pos-reverse-cong p))
lemma-×-reverse-cong {neg a} {neg b} c p = cong neg (ℕ⁺.lemma-×-reverse-cong (lemma-neg-reverse-cong p))

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

-- Unprovable TODO change
lemma-·-reverse-cong : {a b c : ℤ} → a · c ≡ b · c → a ≡ b
lemma-·-reverse-cong {a} {b} {zero}  p = {!!}
lemma-·-reverse-cong {a} {b} {pos c} p = {!!}
lemma-·-reverse-cong {a} {b} {neg c} p = {!!}
