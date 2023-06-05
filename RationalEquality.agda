{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.PropositionalEquality as ≡ hiding (cong; sym; trans)

open import Rational as ℚ  using (ℚ; _/_; num; den; _·_)
open import Natural+ as ℕ⁺ using (ℕ⁺; one; succ)
open import Integer  as ℤ  using (ℤ; zero; pos; neg; _×_)
open import Option

module RationalEquality where
infix 5 _≅_
data _≅_ : ℚ → ℚ → Set where
  eq : {x y : ℚ} → num x × den y ≡ num y × den x → x ≅ y

≡→≅ : {x y : ℚ} → x ≡ y → x ≅ y
≡→≅ refl = eq refl

module ≅-Reasoning where
  cong : {x y : ℚ} → (f : ℚ → ℚ) → x ≅ y → f x ≅ f y
  cong {x} {y} f (eq p) = eq {!!}

  sym : {x y : ℚ} → x ≅ y → y ≅ x
  sym (eq p) = eq (≡.sym p)

  trans : {x y z : ℚ} → x ≅ y → y ≅ z → x ≅ z
  trans (eq p) (eq q) = eq {!!}

  infixr 2 _≅⟨_⟩_ _≅⟨⟩_
  _≅⟨_⟩_ : {y z : ℚ} → (x : ℚ) → x ≅ y → y ≅ z → x ≅ z
  x ≅⟨ p ⟩ q = trans p q
  
  _≅⟨⟩_ : {y : ℚ} → (x : ℚ) → (q : x ≅ y) → x ≅ y
  x ≅⟨⟩ q = q
  
  infix  3 _∎
  _∎ : (x : ℚ) → x ≅ x
  x ∎ = eq refl
  
  infix  1 begin_
  begin_ : {x y : ℚ} → x ≅ y → x ≅ y
  begin p = p

open ≅-Reasoning

lemma-one : {n : ℕ⁺} → pos one / one ≅ pos n / n
lemma-one = eq (≡.cong pos (≡.sym ℕ⁺.lemma-×-one))

lemma-·-one : {x : ℚ} {n : ℕ⁺} → x · (pos n / n) ≅ x
lemma-·-one {x} {n} = begin
  x · (pos n / n)     ≅⟨ sym (cong (x ·_) lemma-one) ⟩
  x · (pos one / one) ≅⟨ ≡→≅ ℚ.lemma-·-one ⟩
  x                   ∎
