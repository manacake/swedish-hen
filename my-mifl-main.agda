module my-mifl-main where

import parse
open import lib
open import mifl

module parsem = parse ptr state aut
open parsem
open parsem.parse rrs

--- PRINT MIFL ---
process-type : type → string
process-type (TypSym s) = s
process-type (TypArr t u) = process-type t ^ " -> " ^ process-type u
process-type (TypPar v) = "(" ^ process-type v ^ ")"

process-term : term → string
process-term (TrmSym s) = s
process-term (TrmApp t u) = process-term t ^ " " ^ process-term u
process-term (TrmPar v) = "(" ^ process-term v ^ ")"

process-eq : eqls → string
process-eq (Eqlist t u e) = process-term t ^ " = " ^ process-term u ^ " ." ^ "\n" ^ process-eq e
process-eq (EqlsNil) = "\n"

process-fn : func → string
process-fn (FnDec s t e) = "fun " ^ s ^ " : " ^ process-type t ^ "\n" ^ process-eq e

process-dtcon : dtconstr → string
process-dtcon (DtCon s t dtc) = " " ^ s ^ " : " ^ process-type t ^ "\n" ^ process-dtcon dtc
process-dtcon (DtNil) = "\n"

process-dt : dt → string
process-dt (DtDec s dtd) = "data " ^ s ^ " where" ^ "\n" ^ process-dtcon dtd

process-cmd : cmd → string
process-cmd (Datatype d) = process-dt d
process-cmd (Function f) = process-fn f

process-cmds : commands → string
process-cmds (Cmds c) = process-cmd c
process-cmds (Nxtcmd c nc) = process-cmd c ^ process-cmds nc

--- EMIT JAVA ---
bp : string
bp = "public class output { \n"
placeholder : string
placeholder = "nat main = (suc zero);\nSystem.out.println(main.toString());\n}\n"

det-v : string → string
det-v "zero" = "0"
det-v "suc" = "1" 
det-v _ = "0"

get-h : 𝕃 string → string
get-h [] = ""
get-h (x :: xs) = x

jv-type : type → 𝕃 string
jv-type (TypSym s) = [ s ]
jv-type (TypArr t u) = jv-type t ++ jv-type u
jv-type (TypPar v) = jv-type v

dt-tostr : string → ℕ → string
dt-tostr s 0 = "public String toString() {\n\treturn '" ^ s ^ "';\n}\n"
dt-tostr s 1 = "public String toString() {\n\treturn '(" ^ s ^ " ' + (x1.toString()) + ')';\n}\n"
dt-tostr _ _ = ""

dt-params : type → ℕ
dt-params (TypSym s) = 0
dt-params (TypArr t u) = 1 + dt-params u
dt-params (TypPar v) = dt-params v

dt-param : ℕ → string → string
dt-param 0 _ = ") {"
dt-param 1 s = s ^ " x1) {\n\tthis.x1 = x1;"
dt-param 2 s = s ^ " x1, " ^ s ^ " x2) {\n\tthis.x1 = x1;\n\tthis.x2 = x2;"
dt-param _ _ = ""

more : ℕ → string → string
more 0 _ = ""
more 1 s = "public " ^ s ^ " get_x1() {\n\treturn x1;\n}\n"
more _ _ = ""

dt-subc : string → type → string
dt-subc s t = "public " ^ s ^ "(" ^ dt-param (dt-params t) (get-h (jv-type t)) ^ "\n}\n"

dt-class : dtconstr → string
dt-class (DtCon s t dtc) = "public static class " ^ s ^ " extends " ^ get-h (jv-type t) 
  ^ " {\n\tpublic int getTag() {\n\treturn " ^ s ^ "_TAG;\n}\n" ^ dt-subc s t ^ 
  more (dt-params t) (get-h (jv-type t)) ^ dt-tostr s (dt-params t) ^ dt-class dtc
dt-class (DtNil) = "}\n"

dt-body : dtconstr → string
dt-body (DtCon s t dtc) = "\tpublic static int " ^ s ^ "_TAG = " ^ det-v s ^ ";" ^ "\n" ^ dt-body dtc
dt-body (DtNil) = "\tpublic abstract int getTag();\n}\n"

dt-head : string → string
dt-head s = "public static abstract class " ^ s ^ " {\n"

fn-head : string → string
fn-head s = "public static void " ^ s ^ "(String[] args) {\n"

jv-f : func → string
jv-f (FnDec s t e) = fn-head s ^ placeholder

jv-dt : dt → string
jv-dt (DtDec s dtd) = dt-head s ^ dt-body dtd ^ dt-class dtd

jv-cmd : cmd → string
jv-cmd (Datatype d) = jv-dt d
jv-cmd (Function f) = jv-f f

jv-cmds : commands → string
jv-cmds (Cmds c) = jv-cmd c
jv-cmds (Nxtcmd c nc) = jv-cmd c ^ jv-cmds nc ^ "\n}\n"

--- START HERE ---
process-start : (printMifl : 𝔹) → (emitJava : 𝔹) → start → string
process-start tt ff (Strt c) = process-cmds c
process-start tt tt (Strt c) = process-cmds c ^ bp ^ jv-cmds c
process-start ff tt (Strt c) = bp ^ jv-cmds c
process-start ff ff (Strt c) = ""

process : (printMifl : 𝔹) → (emitJava : 𝔹) → Run → string
process b b2 (_ :: _ :: ParseTree (parsed-start p) :: _ :: _ :: []) = process-start b b2 p
process _ _ r = "Parsing failure (run with -" ^ "-showParsed).\n"

putStrRunIf : 𝔹 → Run → IO ⊤
putStrRunIf tt r = putStr (Run-to-string r) >> putStr "\n"
putStrRunIf ff r = return triv

processArgs : (showRun : 𝔹) → (showParsed : 𝔹) → (printMifl : 𝔹) → (emitJava : 𝔹) → 𝕃 string → IO ⊤ 
processArgs showRun showParsed printMifl emitJava (x :: []) = (readFiniteFile x) >>= processText
  where processText : string → IO ⊤
        processText x with runAut x
        processText x | s with s
        processText x | s | inj₁ _ = putStr (runState-to-string s) >> putStr "\nCannot proceed to parsing.\n"
        processText x | s | inj₂ r with putStrRunIf showRun r | rewriteRun r
        processText x | s | inj₂ r | sr | r' with putStrRunIf showParsed r'
        processText x | s | inj₂ r | sr | r' | sr' = sr >> sr' >> putStr (process printMifl emitJava r')
                                     
processArgs showRun showParsed printMifl emitJava ("--printMifl" :: xs) = processArgs showRun showParsed tt emitJava xs
processArgs showRun showParsed printMifl emitJava ("--emitJava" :: xs) = processArgs showRun showParsed printMifl tt xs

processArgs showRun showParsed printMifl emitJava ("--showRun" :: xs) = processArgs tt showParsed printMifl emitJava xs 
processArgs showRun showParsed printMifl emitJava ("--showParsed" :: xs) = processArgs showRun tt printMifl emitJava xs 
processArgs showRun showParsed printMifl emitJava (x :: xs) = putStr ("Unknown option " ^ x ^ "\n")
processArgs showRun showParsed printMifl emitJava [] = putStr "Please run with the name of a file to process.\n"

main : IO ⊤
main = getArgs >>= processArgs ff ff ff ff

