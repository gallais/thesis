\begin{code}
module Relation.Binary.PropositionalEquality.Extra where

open import Relation.Binary.PropositionalEquality public

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v s t} → x ≡ y → u ≡ v → s ≡ t → f x u s ≡ f y v t
cong₃ f refl refl refl = refl

\end{code}
