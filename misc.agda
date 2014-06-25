module misc where

open import lib

xor-same : ∀ {b : 𝔹} → b xor b ≡ ff
xor-same {tt} = refl
xor-same {ff} = refl

xor-comm : ∀ {b1 b2 : 𝔹} → b1 xor b2 ≡ b2 xor b1
xor-comm {tt}{tt} = refl
xor-comm {tt}{ff} = refl
xor-comm {ff}{tt} = refl
xor-comm {ff}{ff} = refl

+perm3 : ∀ (w x y z : ℕ) → (w + x) + (y + z) ≡ (w + y) + (x + z)
+perm3 0 x y z rewrite +perm x y z = refl
+perm3 (suc w) x y z rewrite +perm3 w x y z = refl

-- helper lemma for parity-ph
!not-parity : ∀ (x : ℕ) → ~ (~ parity x) ≡ parity x
!not-parity 0 = refl
!not-parity 1 = refl
!not-parity (suc (suc x)) rewrite !not-parity x | !not-parity x = refl
-- helper lemma for parity-pow
parity-ph : ∀ (x : ℕ) → parity x && parity x ≡ parity x
parity-ph 0 = refl
parity-ph 1 = refl
parity-ph (suc (suc x)) rewrite !not-parity x | parity-ph x = refl

parity-pow : ∀ (x y : ℕ) → iszero y ≡ ff → parity (x pow y) ≡ parity x
parity-pow x 0 ()
parity-pow x 1 p rewrite *1 {x} = refl
parity-pow x (suc (suc y)) p with parity-pow x (suc y)
... | q rewrite parity-mult x (x * x pow y) | parity-mult x (x pow y) | q refl | parity-ph x = refl

parity-pow2 : ∀ (y : ℕ) → iszero y ≡ ff → parity (2 pow y) ≡ ff
parity-pow2 0 p = p
parity-pow2 1 p = refl
parity-pow2 (suc (suc y)) p with parity-pow2 (suc y) refl
... | q rewrite +0 (2 pow (suc y)) | parity-add (2 pow (suc y)) (2 pow (suc y)) | q = refl

+∸ : ∀ (x y z : ℕ) → (x + y) ∸ z ≡ (x ∸ z) + (y ∸ (z ∸ x))
+∸ 0 y 0 = refl
+∸ (suc x) y 0 = refl
+∸ 0 y (suc z) = refl
+∸ (suc x) y (suc z) = +∸ x y z

::++ : ∀{ℓ}{A : Set ℓ}(a : A)(l1 l2 : 𝕃 A) → a :: (l1 ++ l2) ≡ (a :: l1) ++ l2
::++ a [] l2 = refl
::++ a l1 l2 = refl

repeat-++ : ∀{ℓ}{A : Set ℓ} (n m : ℕ) (a : A) → (repeat n a) ++ (repeat m a) ≡ repeat (n + m) a
repeat-++ 0 m a = refl
repeat-++ (suc n) m a rewrite repeat-++ n m a = refl
