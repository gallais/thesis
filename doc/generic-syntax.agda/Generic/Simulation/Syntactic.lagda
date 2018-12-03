\begin{code}
module Generic.Simulation.Syntactic where

open import Size
open import Data.List hiding (lookup)
open import Function
open import Relation.Binary.PropositionalEquality

open import Data.Var.Varlike
open import Data.Environment
open import Data.Relation
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Zip
open import Generic.Simulation

open Simulation

module _ {I : Set} {d : Desc I} where

 RenExt : Simulation d Renaming Renaming Eqᴿ Eqᴿ
 RenExt .thᴿ   = λ ρ → cong (lookup ρ)
 RenExt .varᴿ  = cong `var
 RenExt .algᴿ  = λ _ _ →
   cong `con ∘ zip^reify Eqᴿ (reifyᴿ Eqᴿ Eqᴿ (vl^Refl vl^Var)) d

 SubExt : Simulation d Substitution Substitution Eqᴿ Eqᴿ
 SubExt .thᴿ   = λ ρ → cong (ren ρ)
 SubExt .varᴿ  = id
 SubExt .algᴿ  = λ _ _ →
   cong `con ∘ zip^reify Eqᴿ (reifyᴿ Eqᴿ Eqᴿ (vl^Refl vl^Tm)) d

module _ {I : Set} {d : Desc I} where

 RenSub : Simulation d Renaming Substitution VarTmᴿ Eqᴿ
 RenSub .varᴿ  = id
 RenSub .thᴿ   = λ { _ refl → refl }
 RenSub .algᴿ  = λ _ _ →
   cong `con ∘ zip^reify VarTmᴿ (reifyᴿ VarTmᴿ Eqᴿ vl^VarTm) d

 rensub : {Γ Δ : List I} (ρ : Thinning Γ Δ) {i : I} (t : Tm d ∞ i Γ) → ren ρ t ≡ sub (`var <$> ρ) t
 rensub ρ = Simulation.sim RenSub (packᴿ (λ _ → refl))
\end{code}
