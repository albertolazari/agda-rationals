{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.PropositionalEquality as ≡ hiding (cong; sym; trans)
open import Relation.Nullary.Negation
open ≡-Reasoning renaming (begin_ to ≡-begin_; _∎ to _≡-∎)

open import Natural+ as ℕ⁺ using (ℕ⁺; one; succ)
open import Integer  as ℤ  using (ℤ; zero; pos; neg; _×_)
open import Rational as ℚ  using (ℚ; _/_; num; den; ℤ-den; _·_)

module RationalEquivalence where
infix 5 _≈_
data _≈_ : ℚ → ℚ → Set where
  eq : {x y : ℚ} → num x ℤ.· ℤ-den y ≡ num y ℤ.· ℤ-den x → x ≈ y

lemma-·-cong : {x y : ℚ} → (z : ℚ) → x ≈ y → x · z ≈ y · z
lemma-·-cong {a / b} {c / d} z (eq p) = eq (≡-begin
    num ((a / b) · z) ℤ.· ℤ-den ((c / d) · z) ≡⟨ ≡.cong (ℤ._· ℤ-den ((c / d) · z)) (aux-·-num a b z) ⟩
    (a ℤ.· num z) ℤ.· ℤ-den ((c / d) · z)     ≡⟨ ≡.cong (ℤ._·_ (a ℤ.· num z)) (aux-·-den c d z) ⟩
    (a ℤ.· num z) ℤ.· (pos d ℤ.· ℤ-den z)     ≡⟨ ℤ.lemma-·-swap-inner a (num z) (pos d) (ℤ-den z) ⟩
    (a ℤ.· pos d) ℤ.· (num z ℤ.· ℤ-den z)     ≡⟨ ≡.cong (ℤ._· (num z ℤ.· ℤ-den z)) p ⟩
    (c ℤ.· pos b) ℤ.· (num z ℤ.· ℤ-den z)     ≡⟨ ℤ.lemma-·-swap-inner c (pos b) (num z) (ℤ-den z) ⟩
    (c ℤ.· num z) ℤ.· (pos b ℤ.· ℤ-den z)     ≡⟨ ≡.sym (≡.cong (ℤ._·_ (c ℤ.· num z)) (aux-·-den a b z)) ⟩
    (c ℤ.· num z) ℤ.· ℤ-den ((a / b) · z)     ≡⟨ ≡.sym (≡.cong (ℤ._· ℤ-den ((a / b) · z)) (aux-·-num c d z)) ⟩
    num ((c / d) · z) ℤ.· ℤ-den ((a / b) · z) ≡-∎
  )
  where
  aux-·-num : (a : ℤ) → (b : ℕ⁺) → (x : ℚ) → num ((a / b) · x) ≡ a ℤ.· num x 
  aux-·-num a b (c / d) = refl

  aux-·-den : (a : ℤ) → (b : ℕ⁺) → (x : ℚ) → ℤ-den ((a / b) · x) ≡ pos b ℤ.· ℤ-den x
  aux-·-den a b x = ≡-begin
    ℤ-den ((a / b) · x) ≡⟨ aux a b x ⟩
    pos (b ℕ⁺.× den x)  ≡⟨ lemma-·-swap₂ b (den x) ⟩
    pos b ℤ.· pos (den x)   ≡⟨ ≡.cong (pos b ℤ.·_) (lemma-·-swap₁ x) ⟩
    pos b ℤ.· ℤ-den x   ≡-∎
    where
    aux : (a : ℤ) → (b : ℕ⁺) → (x : ℚ) → ℤ-den ((a / b) · x) ≡ pos (b ℕ⁺.× den x)
    aux a b (c / d) = refl

    lemma-·-swap₂ : (x y : ℕ⁺) → pos (x ℕ⁺.× y) ≡ pos x ℤ.· pos y
    lemma-·-swap₂ x one = ≡.cong pos ℕ⁺.lemma-×-one
    lemma-·-swap₂ x (succ y) = ≡.cong pos (ℕ⁺.lemma-×-commutative x (succ y))

    lemma-·-swap₁ : (x : ℚ) → pos (den x) ≡ ℤ-den x
    lemma-·-swap₁ (a / b) = refl


sym : {x y : ℚ} → x ≈ y → y ≈ x
sym (eq p) = eq (≡.sym p)

module Trans where
  {-
  Reasoning behind trans proof
  ============================
  --- Step 1 ---
  p: a · d ≡ c · b
  q: c · f ≡ e · d
  ----------------------------------------- aux
  a₁: (a · d) · (c · f) ≡ (c · b) · (e · d)
  
  a d c f
  ----------------------------------------- lemma-·-swap₂
  a₂: (a · d) · (c · f) ≡ (a · f) · (c · d)
  
  sym a₁: (c · b) · (e · d) ≡ (a · d) · (c · f)
      a₂: (a · d) · (c · f) ≡ (a · f) · (c · d)
  --------------------------------------------- trans
  step₁ : (c · b) · (e · d) ≡ (a · f) · (c · d)
  
  --- Step 2 ---
  c b e d
  ----------------------------------------- lemma-·-swap₁
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

  aux : {a b c d : ℤ} → a ≡ b → c ≡ d
    → a ℤ.· c ≡ b ℤ.· d
  aux refl refl = refl
  
  trans : {x y z : ℚ} → x ≈ y → y ≈ z → x ≈ z
  trans {a / b} {c / d} {e / f} (eq p) (eq q)
    with aux p q
    with ℤ.lemma-·-swap₂ a (pos d) c (pos f)
  ... | a₁ | a₂
    with ≡.trans (≡.sym a₁) a₂
    with ℤ.lemma-·-swap₁ c (pos b) e (pos d)
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
  x · (pos n / n)     ≈⟨ ≡→≈ (ℚ.lemma-·-commutative x (pos n / n)) ⟩
  (pos n / n) · x     ≈⟨ lemma-·-cong x lemma-one ⟩
  (pos one / one) · x ≈⟨ ≡→≈ (ℚ.lemma-·-commutative (pos one / one) x) ⟩
  x · (pos one / one) ≈⟨ ≡→≈ ℚ.lemma-·-one ⟩
  x                   ∎

infix 5 _≉_
_≉_ : ℚ → ℚ → Set
_≉_ x y = ¬ (x ≈ y)

lemma-√2-∉-ℚ : {x : ℚ} → x · x ≉ pos (succ one) / one
lemma-√2-∉-ℚ {zero  / b} = {!!}
lemma-√2-∉-ℚ {pos a / b} = {!!}
lemma-√2-∉-ℚ {neg a / b} = {!!}
