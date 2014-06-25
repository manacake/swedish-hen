module my-gclang-main where

import parse
open import lib
open import list-merge-sort ℕ _<_
open import gclang

module parsem = parse ptr state aut
open parsem
open parsem.parse rrs

{- a cell is a nested pair of the form (extra, fielda, fieldb),
   where each of the components is either nothing or else
   just N.  This N can be any extra data needed by the 
   memory-management algorithm, in the case of the component
   called "extra".  For fielda and fieldb, N is the address
   of another cell. -}
cell : Set
cell = (maybe ℕ) × (maybe ℕ) × (maybe ℕ)
mem : Set
mem = maybe ℕ × 𝕃 ℕ × 𝕃 cell
bmem : Set
bmem = 𝔹 × mem
{- an algorithm is just a name for a particular memory-management
  algorithm which should be applied by process-start -}
data algorithm : Set where
  no-mem-management : algorithm
  ref-counting : algorithm
  mark-and-sweep : algorithm
  copying : algorithm

test-mem : mem
test-mem = ( nothing , 3 :: 1 :: 2 :: [] , repeat 3 ( nothing , nothing , nothing ) )

---for looking @ parts in memory
get0 : mem → maybe ℕ
get0 ( n , _ , _ ) = n
get1 : mem → 𝕃 ℕ
get1 ( _ , ln , _ ) = ln
get2 : mem → 𝕃 cell
get2 ( _ , _ , lc ) = lc
getb : bmem → 𝔹
getb ( b , m ) = b
getm : bmem → mem
getm ( b , m ) = m
geth : 𝕃 ℕ → ℕ
geth (x :: xs) = x
geth [] = 0 -- doesn't happen
getch : 𝕃 cell → cell
getch (x :: xs) = x
getch [] = (nothing , nothing , nothing) -- doesn't happen
gett : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A
gett (x :: xs) = xs
gett [] = []

process-num : string → ℕ
process-num s with string-to-ℕ s
process-num s | nothing = 0
process-num s | just s' = s'

field-to-string : maybe ℕ → string
field-to-string nothing = "-"
field-to-string (just x) = ℕ-to-string x

cell-to-string : cell → string
cell-to-string (extra , fa , fb) = field-to-string extra ^ " : " ^ field-to-string fa ^ " . " ^ field-to-string fb ^ "\n"

mem-to-string : mem → string
mem-to-string (global-extra , roots , cells) = "global extra: " ^ (field-to-string global-extra) 
        ^ "\nroots: " ^ 𝕃-to-string ℕ-to-string " " (merge-sort roots) ^ "\n" ^ string-concat (map cell-to-string cells)

mem-to-graphviz : mem → string
mem-to-graphviz h = "not implemented yet"

dumpMems-h : ℕ → 𝕃 mem → IO ⊤
dumpMems-h n [] = return triv
dumpMems-h n (h :: hs) = writeFile ("mem"^(ℕ-to-string n)^".txt") (mem-to-string h) >> 
                          writeFile ("mem"^(ℕ-to-string n)^".gv") (mem-to-graphviz h) >> 
                          dumpMems-h (suc n) hs

dumpMems : 𝕃 mem → IO ⊤
dumpMems hs = dumpMems-h 0 hs

---checks if a location is in the root list---
root-memb : ℕ → 𝕃 ℕ → 𝔹
root-memb n [] = ff
root-memb n (x :: xs) with n =ℕ x
root-memb n (x :: xs) | tt = tt
root-memb n (x :: xs) | ff = root-memb n xs

add-root : ℕ → mem → mem
add-root i (x , ln , lc) = (x , ln ++ [ i ] , lc)

---functions for assign
process-1f : one-field → string
process-1f (FieldA) = "a"
process-1f (FieldB) = "b"
process-locnull : loc-or-null → string
process-locnull (Loc i) = i
process-locnull (Null) = "null"

find-val : string → maybe ℕ
find-val "null" = nothing
find-val s = just (process-num s)

insrt-cell-h : string → string → cell → cell
insrt-cell-h "a" n (e , _ , b) = (e , find-val n , b)
insrt-cell-h "b" n (e , a , _) = (e , a , find-val n)
insrt-cell-h _ _ c = c -- this doesn't happen

insrt-cell : string → string → 𝕃 cell → 𝕃 cell
insrt-cell ab n (x :: xs) = (insrt-cell-h ab n x) :: xs
insrt-cell _ _ [] = [] -- this doesn't happen

assign-h : mem → 𝕃 cell → mem
assign-h (x , y , z) lc = (x , y , lc)

---find the correct cell to insert value
assign : ℕ → string → string → 𝕃 cell → 𝕃 cell → 𝕃 cell
assign 0 ab n (x :: xs) cs = cs ++ insrt-cell ab n (x :: xs)
assign (suc i) ab n (x :: xs) cs = assign i ab n xs (cs ++ [ x ])
assign _ _ _ [] [] = [] -- this doesn't happen
assign _ _ _ [] (c :: cs) = [] -- this doesn't happen

---functions for DropRoot
switch-loc : mem → 𝕃 ℕ → mem
switch-loc (x , y , z) ln = (x , ln , z)

drop-root : ℕ → 𝕃 ℕ → 𝕃 ℕ → 𝕃 ℕ
drop-root i l (x :: xs) with i =ℕ x
drop-root i l (x :: xs) | tt = l ++ xs
drop-root i l (x :: xs) | ff = drop-root i (l ++ [ x ]) xs
drop-root i l [] = []

---functions for mark-and-sweep algorithm---
---this will return a marked list of cells 
markit : cell → 𝕃 cell → 𝕃 cell
markit (e , a , b) lc = (just 1 , a , b) :: lc

bmark : cell → 𝔹
bmark (nothing , _ , _) = ff
bmark (just 1 , _ , _) = tt
bmark (_ , _ , _) = ff -- doesn't happen

bval : cell → ℕ
bval (_ , _ , nothing) = 0 --doesn't happen
bval (_ , _ , (just n)) = n

---find the correct cell to start traversal
find-cell : ℕ → 𝕃 cell → 𝕃 cell → 𝕃 cell
find-cell2 : ℕ → 𝕃 cell → cell

process-cell : 𝕃 cell → 𝕃 cell → 𝕃 cell
process-cell cs (x :: xs) with bmark (find-cell2 (bval x) (cs ++ (x :: xs)))
process-cell cs (x :: xs) | tt = cs ++ (x :: xs)
process-cell cs (x :: xs) | ff = (find-cell (bval x) (cs ++ (x :: xs)) [])
process-cell _ [] = [] -- doesn't happen

find-cell 0 (x :: xs) cs = process-cell cs (markit x xs)
find-cell (suc n) (x :: xs) cs = find-cell n xs (cs ++ [ x ])
find-cell _ _ _ = [] -- doesn't happen
find-cell2 0 (x :: xs) = x
find-cell2 (suc n) (x :: xs) = find-cell2 n xs
find-cell2 _ _ = (nothing , nothing , nothing) -- doesn't happen

checkmark : cell → 𝔹
checkmark (just 1 , _ , _) = tt
checkmark (nothing , _ , _) = ff
checkmark (_ , _ , _) = ff --doesn't happen

unmark : cell → 𝕃 cell → 𝕃 cell
unmark (e , a , b) lc = (nothing , a , b) :: lc

recycle : cell → 𝕃 cell → 𝕃 cell
recycle (e , a , b) lc = (nothing , nothing , nothing) :: lc

sweep-h : 𝕃 cell → 𝕃 cell
sweep-h (x :: xs) with checkmark x
sweep-h (x :: xs) | tt = unmark x xs
sweep-h (x :: xs) | ff = recycle x xs
sweep-h [] = [] -- doesn't happen

sweep : ℕ → 𝕃 cell → 𝕃 cell → 𝕃 cell
sweep 0 lc cs = cs
sweep (suc n) lc cs = sweep n (gett (sweep-h lc)) (cs ++ [ getch (sweep-h lc) ])

---process each command---
process-cmd : cmd → mem → string → bmem
process-cmd (AddRoot i) m s with root-memb (process-num i) (get1 m)
process-cmd (AddRoot i) m s | tt = (ff , m)
process-cmd (AddRoot i) m s | ff = (ff , add-root (process-num i) m )
process-cmd (Assign i ab n) m s = 
    (ff ,  assign-h m (assign (process-num i) (process-1f ab) (process-locnull n) (get2 m) []) )
process-cmd (DropRoot i) m s = (ff , switch-loc m (drop-root (process-num i) [] (get1 m)) )

process-cmd Gc (x , [] , z) "ms" = (ff , (x , [] , (sweep (length z) z []) ))
process-cmd Gc (x , y , z) "ms" = (ff , (x , y , (sweep (length z) (find-cell (geth y) z []) [])) )
process-cmd Gc m _ = (ff , m)
process-cmd Snapshot m _ = (tt , m)

process-bmem : bmem → 𝕃 mem
process-bmem (ff , m) = []
process-bmem (tt , m) = [ m ]

process-cmds : cmds → mem → string → 𝕃 mem
process-cmds (CmdsLast c) m s = process-bmem (process-cmd c m s)
process-cmds (CmdsNext c cs) m s = process-bmem (process-cmd c m s) ++
    (process-cmds cs (getm (process-cmd c m s)) s )

---initializing the heap---
set-heap-h : ℕ → mem
set-heap-h n = ( nothing , [] , repeat n ( nothing , nothing , nothing ) )

set-heap : init-heap → mem
set-heap (InitHeap n) = set-heap-h (process-num n)

---start here---
--your process start will return a mem list of how your memory looked at each "snapshot"
process-start : start → algorithm → 𝕃 mem
process-start (Strt h cs) no-mem-management = process-cmds cs (set-heap h) "nmm"
process-start (Strt h cs) ref-counting = []
process-start (Strt h cs) mark-and-sweep = process-cmds cs (set-heap h) "ms"
process-start (Strt h cs) copying = []

process : Run → algorithm → 𝕃 mem ⊎ string
process (_ :: _ :: ParseTree (parsed-start p) :: _ :: _ :: []) a = inj₁ (process-start p a)
process r _ = inj₂ ("Parsing failure (run with -" ^ "-showParsed).\n")

putStrRunIf : 𝔹 → Run → IO ⊤
putStrRunIf tt r = putStr (Run-to-string r) >> putStr "\n"
putStrRunIf ff r = return triv

processArgs : (showRun : 𝔹) → (showParsed : 𝔹) → (a : algorithm) → 𝕃 string → IO ⊤ 
processArgs showRun showParsed a (x :: []) = (readFiniteFile x) >>= processText
  where processText : string → IO ⊤
        processText x with runAut x
        processText x | s with s
        processText x | s | inj₁ _ = putStr (runState-to-string s) >> putStr "\nCannot proceed to parsing.\n"
        processText x | s | inj₂ r with putStrRunIf showRun r | rewriteRun r
        processText x | s | inj₂ r | sr | r' with putStrRunIf showParsed r' | process r' a
        processText x | s | inj₂ r | sr | r' | sr' | inj₁ hs = sr >> sr' >> dumpMems hs
        processText x | s | inj₂ r | sr | r' | sr' | inj₂ m = sr >> sr' >> putStr m
                                     
processArgs showRun showParsed a ("--showRun" :: xs) = processArgs tt showParsed a xs 
processArgs showRun showParsed a ("--showParsed" :: xs) = processArgs showRun tt a xs 
processArgs showRun showParsed a ("--ref-counting" :: xs) = processArgs showRun showParsed ref-counting xs 
processArgs showRun showParsed a ("--mark-and-sweep" :: xs) = processArgs showRun showParsed mark-and-sweep xs 
processArgs showRun showParsed a ("--copying" :: xs) = processArgs showRun showParsed copying xs 
processArgs showRun showParsed a (x :: xs) = putStr ("Unknown option " ^ x ^ "\n")
processArgs showRun showParsed a [] = putStr "Please run with the name of a file to process.\n"

main : IO ⊤
main = getArgs >>= processArgs ff ff no-mem-management

