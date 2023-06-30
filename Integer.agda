{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Natural+ as ℕ⁺ using (ℕ⁺; one; succ)

module Integer where
data ℤ : Set where
  zero : ℤ
  pos  : ℕ⁺ → ℤ
  neg  : ℕ⁺ → ℤ

lemma-pos-≢-zero : {n : ℕ⁺} → (x : ℤ) → x ≡ pos n → x ≢ zero
lemma-pos-≢-zero x refl ()

lemma-neg-≢-zero : {n : ℕ⁺} → (x : ℤ) → x ≡ neg n → x ≢ zero
lemma-neg-≢-zero x refl ()

lemma-pos-injective : {x y : ℕ⁺} → pos x ≡ pos y → x ≡ y
lemma-pos-injective {one}    {one}    p    = refl
lemma-pos-injective {succ x} {succ y} refl = refl

lemma-neg-injective : {x y : ℕ⁺} → neg x ≡ neg y → x ≡ y
lemma-neg-injective {one}    {one}    p    = refl
lemma-neg-injective {succ x} {succ y} refl = refl

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
  
lemma-·-swap₂ : (a b c d : ℤ) → (a · b) · (c · d) ≡ (a · d) · (c · b)
lemma-·-swap₂ a b c d = begin
  (a · b) · (c · d) ≡⟨ cong ((a · b) ·_) (sym (lemma-·-commutative d c)) ⟩
  (a · b) · (d · c) ≡⟨ lemma-·-associative a b (d · c) ⟩
  a · (b · (d · c)) ≡⟨ cong (a ·_) (sym (lemma-·-associative b d c)) ⟩
  a · ((b · d) · c) ≡⟨ cong (a ·_) (cong (_· c) ( lemma-·-commutative b d)) ⟩
  a · ((d · b) · c) ≡⟨ cong (a ·_) (lemma-·-associative d b c) ⟩
  a · (d · (b · c)) ≡⟨ sym (lemma-·-associative a d (b · c)) ⟩
  (a · d) · (b · c) ≡⟨ cong ((a · d) ·_) (lemma-·-commutative b c) ⟩
  (a · d) · (c · b) ∎

lemma-·-swap₁ : (a b c d : ℤ) → (a · b) · (c · d) ≡ (c · b) · (a · d)
lemma-·-swap₁ a b c d = begin
  (a · b) · (c · d) ≡⟨ cong (_· (c · d)) (lemma-·-commutative a b) ⟩
  (b · a) · (c · d) ≡⟨ cong ((b · a) ·_) (lemma-·-commutative c d) ⟩
  (b · a) · (d · c) ≡⟨ lemma-·-swap₂ b a d c ⟩
  (b · c) · (d · a) ≡⟨ cong ((b · c) ·_) (lemma-·-commutative d a) ⟩
  (b · c) · (a · d) ≡⟨ cong (_· (a · d)) (lemma-·-commutative b c) ⟩
  (c · b) · (a · d) ∎

lemma-·-swap-inner : (a b c d : ℤ) → (a · b) · (c · d) ≡ (a · c) · (b · d)
lemma-·-swap-inner a b c d = begin
  (a · b) · (c · d) ≡⟨ lemma-·-associative a b (c · d) ⟩
  a · (b · (c · d)) ≡⟨ cong (a ·_) (begin
    b · (c · d) ≡⟨ sym (lemma-·-associative b c d) ⟩
    (b · c) · d ≡⟨ cong (_· d) (lemma-·-commutative b c) ⟩
    (c · b) · d ≡⟨ lemma-·-associative c b d ⟩
    c · (b · d) ∎
  ) ⟩
  a · (c · (b · d)) ≡⟨ sym (lemma-·-associative a c (b · d)) ⟩
  (a · c) · (b · d) ∎
