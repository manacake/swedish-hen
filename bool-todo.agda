module bool-todo where

open import lib

infixr 4 _imp_ 

_imp_ : 𝔹 → 𝔹 → 𝔹 
tt imp b = b
ff imp b = tt

ff-imp : ∀ (b : 𝔹) → ff imp b ≡ tt
ff-imp tt = refl
ff-imp ff = refl

imp-tt : ∀ (b : 𝔹) → b imp tt ≡ tt
imp-tt tt = refl
imp-tt ff = refl

imp-same : ∀ (b : 𝔹) → b imp b ≡ tt
imp-same tt = refl
imp-same ff = refl

&&-contra : ∀ (b : 𝔹) → b && ~ b ≡ ff
&&-contra tt = refl
&&-contra ff = refl

&&-comm : ∀ (b1 b2 : 𝔹) → b1 && b2 ≡ b2 && b1
&&-comm tt tt = refl
&&-comm tt ff = refl 
&&-comm ff tt = refl
&&-comm ff ff = refl

||-comm : ∀ (b1 b2 : 𝔹) → b1 || b2 ≡ b2 || b1
||-comm tt tt = refl
||-comm tt ff = refl
||-comm ff tt = refl
||-comm ff ff = refl

&&-assoc : ∀ (b1 b2 b3 : 𝔹) → b1 && (b2 && b3) ≡ (b1 && b2) && b3
&&-assoc tt b2 b3 = refl
&&-assoc ff b2 b3 = refl

||-assoc : ∀ (b1 b2 b3 : 𝔹) → b1 || (b2 || b3) ≡ (b1 || b2) || b3
||-assoc tt b2 b3 = refl
||-assoc ff b2 b3 = refl

~-over-&& : ∀ (b1 b2 : 𝔹) → ~ ( b1 && b2 ) ≡ (~ b1 || ~ b2)
~-over-&& tt b = refl
~-over-&& ff b = refl

~-over-|| : ∀ (b1 b2 : 𝔹) → ~ ( b1 || b2 ) ≡ (~ b1 && ~ b2)
~-over-|| tt b = refl
~-over-|| ff b = refl

&&-over-||-l : ∀ (a b c : 𝔹) → a && (b || c) ≡ (a && b) || (a && c)
&&-over-||-l tt b c = refl
&&-over-||-l ff b c = refl

&&-over-||-r : ∀ (a b c : 𝔹) → (a || b) && c ≡ (a && c) || (b && c)
&&-over-||-r tt tt tt = refl
&&-over-||-r tt tt ff = refl
&&-over-||-r tt ff tt = refl
&&-over-||-r tt ff ff = refl
&&-over-||-r ff b c = refl

||-over-&&-l : ∀ (a b c : 𝔹) → a || (b && c) ≡ (a || b) && (a || c)
||-over-&&-l tt b c = refl
||-over-&&-l ff b c = refl

||-over-&&-r : ∀ (a b c : 𝔹) → (a && b) || c ≡ (a || c) && (b || c)
||-over-&&-r tt b c = refl
||-over-&&-r ff tt tt = refl
||-over-&&-r ff tt ff = refl
||-over-&&-r ff ff tt = refl
||-over-&&-r ff ff ff = refl

imp-to-|| : ∀ (b1 b2 : 𝔹) → (b1 imp b2) ≡ (~ b1 || b2)
imp-to-|| tt b = refl
imp-to-|| ff b = refl
