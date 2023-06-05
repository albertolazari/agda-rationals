{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.PropositionalEquality as ≡ hiding (cong; sym; trans)
open ≡-Reasoning renaming (begin_ to ≡-begin_; _∎ to _≡-∎)

open import Natural+ as ℕ⁺ using (ℕ⁺; one; succ)
open import Integer  as ℤ  using (ℤ; zero; pos; neg; _×_)
open import Rational as ℚ  using (ℚ; _/_; num; den; ℤ-den; _·_)
open import Option

module RationalEquality where
infix 5 _≈_
data _≈_ : ℚ → ℚ → Set where
  eq : {x y : ℚ} → num x ℤ.· ℤ-den y ≡ num y ℤ.· ℤ-den x → x ≈ y

cong : {x y : ℚ} → (f : ℚ → ℚ) → x ≈ y → f x ≈ f y
cong {x} {y} f (eq p) = eq {!!}

sym : {x y : ℚ} → x ≈ y → y ≈ x
sym (eq p) = eq (≡.sym p)

{-
a x d = c x b
c x f = e x d

(a x d) x (c x f) = (c x b) x (e x d)
(a x f) x (c x d) = (e x b) x (c x d)

a x f =

e x b
-}
trans : {x y z : ℚ} → x ≈ y → y ≈ z → x ≈ z
trans {a / b} {c / d} {e / f} (eq p) (eq q) = eq {!!}
  where
  aux₁ : (a b c d : ℤ)
    → a ≡ b
    → c ≡ d
    → a ℤ.· c ≡ b ℤ.· d
  aux₁ a b c d refl refl = refl

  aux₂ : (a b c d : ℤ) → (a ℤ.· b) ℤ.· (c ℤ.· d) ≡ (a ℤ.· d) ℤ.· (c ℤ.· b)
  aux₂ a b c d = ≡-begin
    (a ℤ.· b) ℤ.· (c ℤ.· d) ≡⟨ ≡.cong ((a ℤ.· b) ℤ.·_) (≡.sym (ℤ.lemma-·-commutative d c)) ⟩
    (a ℤ.· b) ℤ.· (d ℤ.· c) ≡⟨ ℤ.lemma-·-associative a b (d ℤ.· c) ⟩
    a ℤ.· (b ℤ.· (d ℤ.· c)) ≡⟨ ≡.cong (a ℤ.·_) (≡.sym (ℤ.lemma-·-associative b d c)) ⟩
    a ℤ.· ((b ℤ.· d) ℤ.· c) ≡⟨ ≡.cong (a ℤ.·_) (≡.cong (ℤ._· c) ( ℤ.lemma-·-commutative b d)) ⟩
    a ℤ.· ((d ℤ.· b) ℤ.· c) ≡⟨ ≡.cong (a ℤ.·_) (ℤ.lemma-·-associative d b c) ⟩
    a ℤ.· (d ℤ.· (b ℤ.· c)) ≡⟨ ≡.sym (ℤ.lemma-·-associative a d (b ℤ.· c)) ⟩
    (a ℤ.· d) ℤ.· (b ℤ.· c) ≡⟨ ≡.cong ((a ℤ.· d) ℤ.·_) (ℤ.lemma-·-commutative b c) ⟩
    (a ℤ.· d) ℤ.· (c ℤ.· b) ≡-∎

≡→≈ : {x y : ℚ} → x ≡ y → x ≈ y
≡→≈ refl = eq refl

module ≈-Reasoning where
  infixr 2 _≈⟨_⟩_ _≈⟨⟩_
  _≈⟨_⟩_ : {y z : ℚ} → (x : ℚ) → x ≈ y → y ≈ z → x ≈ z
  x ≈⟨ p ⟩ q = trans p q
  
  _≈⟨⟩_ : {y : ℚ} → (x : ℚ) → (q : x ≈ y) → x ≈ y
  x ≈⟨⟩ q = q
  
  infix 3 _∎
  _∎ : (x : ℚ) → x ≈ x
  x ∎ = eq refl
  
  infix 1 begin_
  begin_ : {x y : ℚ} → x ≈ y → x ≈ y
  begin p = p

open ≈-Reasoning

lemma-one : {n : ℕ⁺} → pos n / n ≈ pos one / one
lemma-one = eq (≡.cong pos (≡.sym ℕ⁺.lemma-×-one))

lemma-·-one : {x : ℚ} {n : ℕ⁺} → x · (pos n / n) ≈ x
lemma-·-one {x} {n} = begin
  x · (pos n / n)     ≈⟨ cong (x ·_) lemma-one ⟩
  x · (pos one / one) ≈⟨ ≡→≈ ℚ.lemma-·-one ⟩
  x                   ∎
