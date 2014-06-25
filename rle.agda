module rle where

open import lib
open import list-todo

data run : Set where
  nonempty-run : 𝔹 → ℕ → (𝕃 ℕ) → run
  empty-run : run

{- for benefit of mac users, who cannot see the blackboard fonts,
   I have put some definitions with names like mac-XXXX to show the 
   types -}
mac-nonempty-run : bool → nat → list nat → run
mac-nonempty-run = nonempty-run

decode : run → 𝕃 𝔹
decode empty-run = []
decode (nonempty-run b n []) = repeat (suc n) b
decode (nonempty-run b n (x :: xs)) = repeat (suc n) b ++ decode (nonempty-run (~ b) x xs)

mac-decode : run → list bool
mac-decode = decode

test-input : 𝕃 𝔹
test-input = ff :: tt :: tt :: tt :: ff :: ff :: []

mac-test-input : list bool
mac-test-input = test-input

decode-test1 = decode (nonempty-run ff 0 (2 :: 1 :: []))

lem-decode-test1 : decode-test1 ≡ test-input
lem-decode-test1 = refl

lem-decode-empty : decode empty-run ≡ []
lem-decode-empty = refl

encodeh : 𝔹 → run → run
encodeh b empty-run = nonempty-run b 0 []
encodeh tt (nonempty-run tt n ns) = nonempty-run tt (suc n) ns
encodeh ff (nonempty-run ff n ns) = nonempty-run ff (suc n) ns
encodeh ff (nonempty-run tt n ns) = nonempty-run ff 0 (n :: ns)
encodeh tt (nonempty-run ff n ns) = nonempty-run tt 0 (n :: ns)

mac-encodeh : bool → run → run
mac-encodeh = encodeh

encode : 𝕃 𝔹 → run
encode [] = empty-run
encode (b :: []) = encodeh b empty-run
encode (b :: bs) = encodeh b (encode bs)

mac-encode : list bool → run
mac-encode = encode 

encode-test1 = encode test-input

lem-encode-test1 : encode-test1 ≡ nonempty-run ff 0 (2 :: 1 :: [])
lem-encode-test1 = refl

lem-encode-empty : encode [] ≡ empty-run 
lem-encode-empty = refl

encodeh-lem : ∀ (b : 𝔹) → encodeh b empty-run ≡ nonempty-run b 0 []
encodeh-lem b = refl

mac-encodeh-lem : ∀ (b : bool) → encodeh b empty-run ≡ nonempty-run b 0 []
mac-encodeh-lem = encodeh-lem

encodeh-lem2 : ∀ (b : 𝔹) (n : ℕ) (ns : 𝕃 ℕ) → encodeh b (nonempty-run (~ b) n ns) ≡ nonempty-run b 0 (n :: ns)
encodeh-lem2 tt n ns = refl
encodeh-lem2 ff n ns = refl

mac-encodeh-lem2 : ∀ (b : 𝔹) (n : ℕ) (ns : 𝕃 ℕ) → encodeh b (nonempty-run (~ b) n ns) ≡ nonempty-run b 0 (n :: ns)
mac-encodeh-lem2 = encodeh-lem2

encodeh-lem3 : ∀ (b : 𝔹)(n : ℕ)(ns : 𝕃 ℕ) → encodeh b (nonempty-run b n ns) ≡ nonempty-run b (suc n) ns
encodeh-lem3 tt n ns = refl
encodeh-lem3 ff n ns = refl

mac-encodeh-lem3 : ∀ (b : bool)(n : nat)(ns : list nat) → encodeh b (nonempty-run b n ns) ≡ nonempty-run b (suc n) ns
mac-encodeh-lem3 = encodeh-lem3

decode-length-neg : ∀ (b : 𝔹) (n : ℕ) (ns : 𝕃 ℕ) → length (decode (nonempty-run b n ns)) ≡ length (decode (nonempty-run (~ b) n ns))

decode-length-neg b n [] rewrite length-repeat n b | length-repeat n (~ b) = refl
decode-length-neg b n (x :: xs) rewrite length-++ (repeat n b) (decode (nonempty-run (~ b) x xs)) | length-++ (repeat n (~ b)) (decode (nonempty-run (~ (~ b)) x xs)) | length-repeat n b | length-repeat n (~ b) | ~~-elim b | decode-length-neg b x xs = refl

mac-decode-length-neg : ∀ (b : bool) (n : nat) (ns : list nat) → length (decode (nonempty-run b n ns)) ≡ length (decode (nonempty-run (~ b) n ns))
mac-decode-length-neg = decode-length-neg

decode-length : ∀ (b : 𝔹) (n : ℕ) (ns : 𝕃 ℕ) → suc (length ns) ≤ length (decode (nonempty-run b n ns)) ≡ tt
decode-length b 0 [] = refl
decode-length b 0 (n :: ns) rewrite decode-length (~ b) n ns = refl
decode-length b (suc n) ns 
  rewrite <≤-trans{length ns}{z = length (decode (nonempty-run b n ns))} (<-suc (length ns)) (decode-length b n ns) = refl

encode-repeat : ∀ (b : 𝔹)(n : ℕ) → encode (repeat (suc n) b) ≡ (nonempty-run b n [])
encode-repeat b 0 = refl
encode-repeat tt (suc n) rewrite encode-repeat tt n = refl
encode-repeat ff (suc n) rewrite encode-repeat ff n = refl

mac-encode-repeat : ∀ (b : bool)(n : nat) → encode (repeat (suc n) b) ≡ (nonempty-run b n [])
mac-encode-repeat = encode-repeat

encodeh-lem : ∀ (b : 𝔹) → encodeh b empty-run ≡ nonempty-run b 0 []
encodeh-lem tt = refl
encodeh-lem ff = refl

decode-encodeh : ∀ (b : 𝔹) (r : run) → decode (encodeh b r) ≡ b :: decode r
decode-encodeh tt (nonempty-run tt n ns) = refl
decode-encodeh ff (nonempty-run ff n ns) = refl
decode-encodeh tt (nonempty-run ff n ns) = refl
decode-encodeh ff (nonempty-run tt n ns) = refl
decode-encodeh b empty-run rewrite encodeh-lem b = refl

decode-encode : ∀ (l : 𝕃 𝔹) → decode (encode l) ≡ l
decode-encode [] = refl
decode-encode (b :: bs) rewrite decode-encodeh b (encode bs) | decode-encode bs = refl

encodeh-lem2 : ∀ (b : 𝔹) (n : ℕ) (ns : 𝕃 ℕ) → encodeh b (nonempty-run (~ b) n ns) ≡ nonempty-run b 0 (n :: ns)
encodeh-lem2 tt n ns = refl
encodeh-lem2 ff n ns = refl

encodeh-lem3 : ∀ (b : 𝔹)(n : ℕ)(ns : 𝕃 ℕ) → encodeh b (nonempty-run b n ns) ≡ nonempty-run b (suc n) ns
encodeh-lem3 tt n ns = refl
encodeh-lem3 ff n ns = refl

encode-decode : ∀ (r : run) → encode (decode r) ≡ r
encode-decode (nonempty-run b 0 []) = encodeh-lem b
encode-decode (nonempty-run b 0 (n :: ns)) rewrite encode-decode (nonempty-run (~ b) n ns) = encodeh-lem2 b n ns
encode-decode (nonempty-run b (suc n) ns) rewrite encode-decode (nonempty-run b n ns) = encodeh-lem3 b n ns
encode-decode empty-run = refl
