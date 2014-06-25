module matrices where

open import lib

t0 : 𝕃 𝔹
t0 = ff :: tt :: tt :: ff :: tt :: []
t1 : 𝕃 𝔹
t1 = tt :: tt :: []
t2 : 𝕃 char
t2 = '1' :: '0' :: '1' :: []

t4 = length t0 ∸ 3

process-num : (d : string) → ℕ
process-num d with string-to-ℕ d
process-num d | nothing = 0
process-num d | just d' = d'

det-shift : (l : 𝕃 𝔹)(s : string)(d : ℕ)(n : ℕ) → 𝕃 𝔹
det-shift [] _ _ _ = [] -- never happens
det-shift (x :: xs) "≪" d _ = (x :: xs) ++ repeat d ff
det-shift (x :: xs) "≫" _ 0 = []
det-shift (x :: xs) "≫" _ (suc n) = x :: det-shift xs "≫" 0 n
det-shift (x :: xs) _ _ _ = [] -- never happens

{- an n by m matrix consists of n rows, where each row is a vector of size m. -}
_by_matrix : ℕ → ℕ → Set
n by m matrix = 𝕍 (𝕍 ℕ m) n

{- The n by m zero matrix is just an n by m matrix where
   every element is 0. -}
zero-matrix : (n m : ℕ) → n by m matrix
zero-matrix n m = repeat𝕍 (repeat𝕍 0 m) n

test-zero-matrix : zero-matrix 2 3 ≡ ((0 :: 0 :: 0 :: []) :: (0 :: 0 :: 0 :: []) :: [])
test-zero-matrix = refl

row-to-string : ∀{m : ℕ} → 𝕍 ℕ m → string
row-to-string r = 𝕍-to-string (ℕ-to-string) (" ") r

{- Convert an n by m matrix to a string.  The format should
   be row1; row2; ...; rown, where each row looks like a1 a2 ... an. -}
matrix-to-string : ∀ {n m : ℕ} → n by m matrix → string
matrix-to-string [] = ""
matrix-to-string (r :: []) = row-to-string r
matrix-to-string (r :: rs) = row-to-string r ^ "; " ^ matrix-to-string rs

test-matrix-to-string : matrix-to-string (zero-matrix 3 4) ≡ "0 0 0 0; 0 0 0 0; 0 0 0 0"
test-matrix-to-string = refl

{- Return the i'th row of the matrix. -}
matrix-row : ∀{n m : ℕ}(i : ℕ) → i < n ≡ tt → n by m matrix → 𝕍 ℕ m
matrix-row i p m = nth𝕍 i p m

{- Get the element in row i, column j from the given n by m
   matrix, where i must be less than n and j less than m. -}
matrix-elt : ∀{n m : ℕ}(i j : ℕ) → i < n ≡ tt → j < m ≡ tt → n by m matrix → ℕ
matrix-elt i j p1 p2 m = nth𝕍 j p2 (matrix-row i p1 m)

{- This is a helper for identity-matrixh below.
   diagonal-𝕍 d n k should return the vector of length n that
   has value d at index k and 0 for every other element -}
diagonal-𝕍 : (d n k : ℕ) → 𝕍 ℕ n
diagonal-𝕍 d 0 k = []
diagonal-𝕍 d (suc n) 0 = [ d ]𝕍 ++𝕍 repeat𝕍 0 n
diagonal-𝕍 d (suc n) (suc k) = [ 0 ]𝕍 ++𝕍 diagonal-𝕍 d n k

{- This is a helper for diagonal-matrix below.
   diagonal-matrixh should return the bottom m rows of the diagonal
   matrix with d along the diagonal -}
diagonal-matrixh : (d n m : ℕ) → m by n matrix
diagonal-matrixh d n 0 = []
diagonal-matrixh d n (suc m) = (diagonal-𝕍 d n (n ∸ (suc m))) :: (diagonal-matrixh d n m)

{- This should return the n by n diagonal matrix (all
   elements 0 except that we have value d down the diagonal from top
   left to bottom right) -}
diagonal-matrix : (d : ℕ) → (n : ℕ) → n by n matrix
diagonal-matrix d n = diagonal-matrixh d n n

identity-matrix : (n : ℕ) → n by n matrix
identity-matrix n = diagonal-matrix 1 n

{- Given a function f which takes an index i and a proof
   that i is less than n, return the vector of length n which looks
   like (f 0 p0) :: (f 1 p1) :: ... :: (f n-1 pn-1).  That is, the
   i'th element of the vector is (f i pi), where pi is the proof that
   i < n. -}
init-𝕍h : ∀{ℓ}{A : Set ℓ}{n : ℕ} → (f : (i : ℕ) → i < n ≡ tt → A) → 𝕍 A n
init-𝕍h{n = 0} f = [] 
init-𝕍h{n = suc n} f = (f n (<-suc n)) :: init-𝕍h{n = n} (λ i p → (f i (<-trans{i}{n}{suc n} p (<-suc n))))

reverse𝕍-helper : ∀{ℓ}{A : Set ℓ}{n m : ℕ} → 𝕍 A n → 𝕍 A m → 𝕍 A (n + m)
reverse𝕍-helper{n = n} h [] rewrite +0 n = h
reverse𝕍-helper{n = n}{suc m} h (x :: xs) rewrite +suc n m = reverse𝕍-helper (x :: h) xs

reverse𝕍 : ∀{ℓ}{A : Set ℓ}{n : ℕ} → 𝕍 A n → 𝕍 A n
reverse𝕍 v = reverse𝕍-helper [] v

init-𝕍 : ∀{ℓ}{A : Set ℓ}{n : ℕ} → (f : (i : ℕ) → i < n ≡ tt → A) → 𝕍 A n
init-𝕍 f = reverse𝕍 (init-𝕍h f)

{- Given the number n of rows and m of columns for the new
   matrix, and a function f, create a new matrix where the element at
   row i, column j is (f i j).  Hint: use init-𝕍 twice.  
-}
create-matrix : ∀{n m : ℕ} → (f : (i j : ℕ) → i < n ≡ tt → j < m ≡ tt → ℕ) → n by m matrix
create-matrix{n}{m} f = init-𝕍 (λ i p → (init-𝕍 (λ j p' → (f i j p p'))))

-- define matrix addition.
_+matrix_ : ∀ {n m : ℕ} → n by m matrix → n by m matrix → n by m matrix
x +matrix y = create-matrix (λ (i j : ℕ) p q → (matrix-elt i j p q x) + (matrix-elt i j p q y))

test-+matrix : (identity-matrix 2) +matrix (zero-matrix 2 2) ≡ (identity-matrix 2)
test-+matrix = refl

test-+matrix2 : (identity-matrix 3) +matrix (identity-matrix 3) ≡ (diagonal-matrix 2 3)
test-+matrix2 = refl

-- switch the rows and columns of the given matrix.
transpose : ∀{n m : ℕ} → n by m matrix → m by n matrix
transpose m = create-matrix (λ i j p q → matrix-elt j i q p m)

{- compute the dot product of two vectors v and u, in the sense
   of linear algebra: (v_0 * u_0) + ... + (v_k-1 * u_k-1), where 
   v_0 :: ... :: v_k-1 :: 0 and u_0 :: ... :: u_k-1 :: 0 are the 
   vectors v and u -}
_·_ : ∀{k : ℕ} → 𝕍 ℕ k → 𝕍 ℕ k → ℕ
[] · [] = 0
(x :: xs) · (y :: ys) = x * y + (xs · ys)

-- define matrix multiplication.  Hint: use matrix-row, _·_, and transpose.
_*matrix_ : ∀{n k m : ℕ} → n by k matrix → k by m matrix → n by m matrix
m *matrix m' = create-matrix (λ i j p q → (matrix-row i p m) · (matrix-row j q (transpose m')))
