{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.PropositionalEquality as ≡ hiding (cong; sym; trans)
open import Relation.Nullary.Negation
open ≡-Reasoning renaming (begin_ to ≡-begin_; _∎ to _≡-∎)

open import Natural+ as ℕ⁺ using (ℕ⁺; one; succ)
open import Integer  as ℤ  using (ℤ; zero; pos; neg; _×_)
open import Rational as ℚ  using (ℚ; _/_; num; den; ℤ-den; _·_)
open import Option

module RationalEquivalence where
infix 5 _≈_
data _≈_ : ℚ → ℚ → Set where
  eq : {x y : ℚ} → num x ℤ.· ℤ-den y ≡ num y ℤ.· ℤ-den x → x ≈ y

-- Not true actually
-- TODO: figure out how to fix
cong : {x y : ℚ} → (f : ℚ → ℚ) → x ≈ y → f x ≈ f y
cong {a / b} {c / d} f (eq p) = eq {!!}

sym : {x y : ℚ} → x ≈ y → y ≈ x
sym (eq p) = eq (≡.sym p)

module Trans where
  {-
  Reasoning behind trans proof
  ============================
  --- Step 1 ---
  p: a · d ≡ c · b
  q: c · f ≡ e · d
  ----------------------------------------- aux₁
  a₁: (a · d) · (c · f) ≡ (c · b) · (e · d)
  
  a d c f
  ----------------------------------------- aux₂
  a₂: (a · d) · (c · f) ≡ (a · f) · (c · d)
  
  sym a₁: (c · b) · (e · d) ≡ (a · d) · (c · f)
      a₂: (a · d) · (c · f) ≡ (a · f) · (c · d)
  --------------------------------------------- trans
  step₁ : (c · b) · (e · d) ≡ (a · f) · (c · d)
  
  --- Step 2 ---
  c b e d
  ----------------------------------------- aux₃
  a₃: (c · b) · (e · d) ≡ (e · b) · (c · d)
  
  sym step₁: (a · f) · (c · d) ≡ (c · b) · (e · d)
      a₃   : (c · b) · (e · d) ≡ (e · b) · (c · d)
  ------------------------------------------------ trans
  step₂    : (a · f) · (c · d) ≡ (e · b) · (c · d)
  
  --- Conclusion ---
  step₂: (a · f) · (c · d) ≡ (e · b) · (c · d)
  -------------------------------------------- lemma-×-injective₂ (d × c) (lemma-pos-injective step₂)
  a · f ≡ e · b
  -}

  aux₁ : {a b c d : ℤ} → a ≡ b → c ≡ d
    → a ℤ.· c ≡ b ℤ.· d
  aux₁ refl refl = refl
  
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
  
  aux₃ : (a b c d : ℤ) → (a ℤ.· b) ℤ.· (c ℤ.· d) ≡ (c ℤ.· b) ℤ.· (a ℤ.· d)
  aux₃ a b c d = ≡-begin
    (a ℤ.· b) ℤ.· (c ℤ.· d) ≡⟨ ≡.cong (ℤ._· (c ℤ.· d)) (ℤ.lemma-·-commutative a b) ⟩
    (b ℤ.· a) ℤ.· (c ℤ.· d) ≡⟨ ≡.cong ((b ℤ.· a) ℤ.·_) (ℤ.lemma-·-commutative c d) ⟩
    (b ℤ.· a) ℤ.· (d ℤ.· c) ≡⟨ aux₂ b a d c ⟩
    (b ℤ.· c) ℤ.· (d ℤ.· a) ≡⟨ ≡.cong ((b ℤ.· c) ℤ.·_) (ℤ.lemma-·-commutative d a) ⟩
    (b ℤ.· c) ℤ.· (a ℤ.· d) ≡⟨ ≡.cong (ℤ._· (a ℤ.· d)) (ℤ.lemma-·-commutative b c) ⟩
    (c ℤ.· b) ℤ.· (a ℤ.· d) ≡-∎
  
  trans : {x y z : ℚ} → x ≈ y → y ≈ z → x ≈ z
  trans {a / b} {c / d} {e / f} (eq p) (eq q)
    with aux₁ p q
    with aux₂ a (pos d) c (pos f)
  ... | a₁ | a₂
    with ≡.trans (≡.sym a₁) a₂
    with aux₃ c (pos b) e (pos d)
  ... | step₁ | a₃
    with ≡.trans (≡.sym step₁) a₃
  trans {zero / b} {zero / d} {zero / f} (eq refl) (eq refl) | a₁ | a₂ | step₁ | a₃ | step₂ = eq refl
  trans {pos a / b} {pos c / d} {pos e / f} (eq p) (eq q) | a₁ | a₂ | step₁ | a₃ | step₂ = eq (≡.cong pos (ℕ⁺.lemma-×-injective₂ (d ℕ⁺.× c) (ℤ.lemma-pos-injective step₂)))
  trans {neg a / b} {neg c / d} {neg e / f} (eq p) (eq q) | a₁ | a₂ | step₁ | a₃ | step₂ = eq (≡.cong neg (ℕ⁺.lemma-×-injective₂ (d ℕ⁺.× c) (ℤ.lemma-pos-injective step₂)))

trans = Trans.trans

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

lemma-zero : {x y : ℕ⁺} → zero / x ≈ zero / y
lemma-zero = eq refl

lemma-one : {n : ℕ⁺} → pos n / n ≈ pos one / one
lemma-one = eq (≡.cong pos (≡.sym ℕ⁺.lemma-×-one))

lemma-·-one : {x : ℚ} {n : ℕ⁺} → x · (pos n / n) ≈ x
lemma-·-one {x} {n} = begin
  x · (pos n / n)     ≈⟨ cong (x ·_) lemma-one ⟩
  x · (pos one / one) ≈⟨ ≡→≈ ℚ.lemma-·-one ⟩
  x                   ∎

lemma-√2-∉-ℚ : {x : ℚ} → ¬ (x · x ≈ pos (succ one) / one)
lemma-√2-∉-ℚ {zero  / b} = {!!}
lemma-√2-∉-ℚ {pos a / b} = {!!}
lemma-√2-∉-ℚ {neg a / b} = {!!}
