module nat-todo where

open import lib

infixl 11 _pow_

_pow_ : ℕ → ℕ → ℕ
x pow 0 = 1
x pow (suc y) = x * (x pow y)

factorial : ℕ → ℕ
factorial 0 = 1
factorial (suc n) = (suc n) * factorial n 

*1 : ∀ {n : ℕ} → n * 1 ≡ n
*1 {0} = refl
*1 {suc n} rewrite *1 {n} = refl

1-pow : ∀ {n : ℕ} → 1 pow n ≡ 1
1-pow {0} = refl
1-pow {(suc n)} rewrite 1-pow {n}= refl

-- helper lemma for factorial-nonzero
fac-!0-help : ∀ (x y : ℕ) → iszero(x + y) ≡ iszero x && iszero y
fac-!0-help 0 y = refl
fac-!0-help (suc x) y = refl

factorial-nonzero : ∀ (n : ℕ) → iszero (factorial n) ≡ ff
factorial-nonzero 0 = refl
factorial-nonzero (suc n) rewrite fac-!0-help (factorial n) (n * factorial n) | factorial-nonzero n = refl

pow+ : ∀ (x y z : ℕ) → x pow (y + z) ≡ (x pow y) * (x pow z)
pow+ x 0 z rewrite +0 (x pow z) = refl
pow+ x (suc y) z rewrite pow+ x y z | *assoc x (x pow y) (x pow z) = refl

nonzero< : ∀ {n : ℕ} → iszero n ≡ ff → 0 < n ≡ tt
nonzero< {0} p = sym p
nonzero< {suc n} p = refl

parity-odd : ∀ (x : ℕ) → parity (x * 2 + 1) ≡ tt
parity-odd 0 = refl
parity-odd (suc x) rewrite parity-odd x = refl

=ℕ-sym : ∀ (x y : ℕ) → (x =ℕ y) ≡ (y =ℕ x)
=ℕ-sym 0 0 = refl
=ℕ-sym (suc x) zero = refl
=ℕ-sym 0 (suc y) = refl
=ℕ-sym (suc x) (suc y) rewrite =ℕ-sym x y = refl

-- another version of addition
_+'_ : ℕ → ℕ → ℕ
0 +' y = y
suc x +' y = x +' (suc y)

--helper lemma for +'0 and +'comm
+'suc : ∀ (x y : ℕ) → x +' (suc y) ≡ suc(x +' y)
+'suc 0 y = refl
+'suc (suc x) y rewrite +'suc x (suc y) = refl

--helper lemma for +'comm
+'0 : ∀ (x : ℕ) → x +' 0 ≡ x
+'0 0 = refl
+'0 (suc x) rewrite +'suc x 0 | +'0 x = refl

+'comm : ∀ (x y : ℕ) → x +' y ≡ y +' x
+'comm 0 y rewrite +'0 y = refl
+'comm (suc x) y rewrite +'suc x y | +'suc y x | +'comm x y = refl

+'-equiv-+ : ∀ (x y : ℕ) → x + y ≡ x +' y
+'-equiv-+ 0 y = refl
+'-equiv-+ (suc x) y rewrite +'suc x y | +'-equiv-+ x y = refl
