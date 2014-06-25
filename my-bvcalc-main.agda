module my-bvcalc-main where

import parse
open import lib
open import bvcalc

open import run ptr aut
module parsem = parse ptr aut
open parsem.parse rrs

-- using with map: given a list of chars(0,1), returns a list of bools
det-char : (c : char) → 𝔹
det-char '0' = ff
det-char '1' = tt
det-char _ = ff 
--using with map: given a list of bools, returns a list of chars
det-bool : (b : 𝔹) → char
det-bool tt = '1'
det-bool ff = '0'
--negates every bool in list
det-neg : (l : 𝕃 𝔹) → 𝕃 𝔹
det-neg [] = []
det-neg (b :: bs) = ~ b :: det-neg bs
--given 2 list of bools and operator string, returns a list of bools
--with operator applied to both lists
det-bitop : (l : 𝕃 𝔹)(l2 : 𝕃 𝔹)(o : string) → 𝕃 𝔹
det-bitop [] [] _ = []
det-bitop [] (y :: ys) "&" = ff :: det-bitop [] ys "&"
det-bitop (x :: xs) [] "&" = ff :: det-bitop xs [] "&"
det-bitop [] (y :: ys) "|" = y :: ys
det-bitop (x :: xs) [] "|" = x :: xs
det-bitop [] (y :: ys) "⊕" = y :: det-bitop [] ys "⊕"
det-bitop (x :: xs) [] "⊕" = x :: det-bitop xs [] "⊕"
det-bitop [] (y :: ys) _ = [] -- never happens
det-bitop (x :: xs) [] _ = [] -- never happens
det-bitop (x :: xs) (y :: ys) "&" = (x && y) :: det-bitop xs ys "&"
det-bitop (x :: xs) (y :: ys) "|" = (x || y) :: det-bitop xs ys "|"
det-bitop (x :: xs) (y :: ys) "⊕" = (x xor y) :: det-bitop xs ys "⊕"
det-bitop (x :: xs) (y :: ys) _ = [] -- never happens
--changes the digit string from shiftop to a ℕ
process-num : (d : string) → ℕ
process-num d with string-to-ℕ d
process-num d | nothing = 0 -- never happens
process-num d | just d' = d'
--given a list of bools, will either add/subtract bits depending
--on shift operator
det-shift : (l : 𝕃 𝔹)(s : string)(d : ℕ)(n : ℕ) → 𝕃 𝔹
det-shift [] _ _ _ = [] -- never happens
det-shift (x :: xs) "≪" d _ = (x :: xs) ++ repeat d ff
det-shift (x :: xs) "≫" _ 0 = []
det-shift (x :: xs) "≫" _ (suc n) = x :: det-shift xs "≫" 0 n
det-shift (x :: xs) _ _ _ = [] -- never happens

process-expr : expr → 𝕃 𝔹
process-expr (Bvlit b) = map det-char (string-to-𝕃char b)
process-expr (Parens p) = process-expr p
process-expr (Neg n) = det-neg (process-expr n)
process-expr (Bitop x o y) = det-bitop (process-expr x) (process-expr y) o
process-expr (Shiftop z s d) = det-shift (process-expr z) s (process-num d) ((length (process-expr z)) ∸ (process-num d))

process-start : start → string
process-start (Bv b) = 𝕃char-to-string (map det-bool (process-expr b)) ^ "\n"

process : Run → string
process (State s0 :: State s2 :: ParseTree (parsed-start p) :: State s3 :: State s1 :: []) = process-start p
process r = "Parsing failure (run with -" ^ "-showParsed).\n"

putStrRunIf : 𝔹 → Run → IO ⊤
putStrRunIf tt r = putStr (Run-to-string r) >> putStr "\n"
putStrRunIf ff r = return triv

processArgs : (showRun : 𝔹) → (showParsed : 𝔹) → 𝕃 string → IO ⊤ 
processArgs showRun showParsed (x :: []) = (readFiniteFile x) >>= processText
  where processText : string → IO ⊤
        processText x with runAut x
        processText x | s with s
        processText x | s | inj₁ _ = putStr (runState-to-string s) >> putStr "\nCannot proceed to parsing.\n"
        processText x | s | inj₂ r with putStrRunIf showRun r | rewriteRun r
        processText x | s | inj₂ r | sr | r' with putStrRunIf showParsed r'
        processText x | s | inj₂ r | sr | r' | sr' = sr >> sr' >> putStr (process r')
                                     
processArgs showRun showParsed ("--showRun" :: xs) = processArgs tt showParsed xs 
processArgs showRun showParsed ("--showParsed" :: xs) = processArgs showRun tt xs 
processArgs showRun showParsed (x :: xs) = putStr ("Unknown option " ^ x ^ "\n")
processArgs showRun showParsed [] = putStr "Please run with the name of a file to process.\n"

main : IO ⊤
main = getArgs >>= processArgs ff ff

