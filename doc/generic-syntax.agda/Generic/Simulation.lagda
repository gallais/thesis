\begin{code}

open import Data.Var hiding (_<$>_; z; s)
open import Data.Relation

module Generic.Simulation {I : Set} {𝓥₁ 𝓥₂ 𝓒₁ 𝓒₂ : I ─Scoped} (𝓡^𝓥  : Rel 𝓥₁ 𝓥₂) (𝓡^𝓒  : Rel 𝓒₁ 𝓒₂) where

open import Size
open import Data.List hiding ([_] ; lookup ; zip)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Relation.Unary

open import Data.Var.Varlike
open import Data.Environment
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Zip

private
  variable
    Γ Δ : List I
    σ : I
    v₁ : 𝓥₁ σ Γ
    v₂ : 𝓥₂ σ Γ
    s : Size
    ρ₁ : (Γ ─Env) 𝓥₁ Δ
    ρ₂ : (Γ ─Env) 𝓥₂ Δ

reifyᴿ : {vl₁ : VarLike 𝓥₁} {vl₂ : VarLike 𝓥₂} (vlᴿ : VarLikeᴿ 𝓡^𝓥 vl₁ vl₂) →
         ∀ Δ σ → {k₁ : Kripke 𝓥₁ 𝓒₁ Δ σ Γ} {k₂ : Kripke 𝓥₂ 𝓒₂ Δ σ Γ} →
         Kripkeᴿ 𝓡^𝓥 𝓡^𝓒 Δ σ k₁ k₂ → rel 𝓡^𝓒 σ (reify vl₁ Δ σ k₁) (reify vl₂ Δ σ k₂)
reifyᴿ vlᴿ []         σ kᴿ = kᴿ
reifyᴿ vlᴿ Δ@(_ ∷ _)  σ kᴿ = kᴿ (freshʳ vl^Var Δ) (VarLikeᴿ.freshˡᴿ vlᴿ _)

record Simulation (d : Desc I) (𝓢₁ : Semantics d 𝓥₁ 𝓒₁) (𝓢₂ : Semantics d 𝓥₂ 𝓒₂) : Set where
  module 𝓢₁ = Semantics 𝓢₁
  module 𝓢₂ = Semantics 𝓢₂
  field  thᴿ   : (ρ : Thinning Γ Δ) → rel 𝓡^𝓥 σ v₁ v₂ → rel 𝓡^𝓥 σ (𝓢₁.th^𝓥 v₁ ρ) (𝓢₂.th^𝓥 v₂ ρ)
         varᴿ  : rel 𝓡^𝓥 σ v₁ v₂ → rel 𝓡^𝓒 σ (𝓢₁.var v₁) (𝓢₂.var v₂)
         algᴿ  : (b : ⟦ d ⟧ (Scope (Tm d s)) σ Γ) → All 𝓡^𝓥 Γ ρ₁ ρ₂ →
                    let  v₁ = fmap d (𝓢₁.body {s = s} ρ₁) b
                         v₂ = fmap d (𝓢₂.body {s = s} ρ₂) b
                    in Zip d (Kripkeᴿ 𝓡^𝓥 𝓡^𝓒) v₁ v₂ → rel 𝓡^𝓒 σ (𝓢₁.alg v₁) (𝓢₂.alg v₂)


  sim   :  ∀ {s} → All 𝓡^𝓥 Γ ρ₁ ρ₂ → (t : Tm d s σ Γ) → rel 𝓡^𝓒 σ (𝓢₁.semantics ρ₁ t) (𝓢₂.semantics ρ₂ t)
  body  :  ∀ {s} → All 𝓡^𝓥 Γ ρ₁ ρ₂ → ∀ Δ j → (t : Scope (Tm d s) Δ j Γ) →
           Kripkeᴿ 𝓡^𝓥 𝓡^𝓒 Δ j (𝓢₁.body ρ₁ Δ j t) (𝓢₂.body ρ₂ Δ j t)

  sim ρᴿ (`var k) = varᴿ (lookupᴿ ρᴿ k)
  sim ρᴿ (`con t) = algᴿ t ρᴿ (zip d (body ρᴿ) t)

  body ρᴿ []       i t = sim ρᴿ t
  body ρᴿ (σ ∷ Δ)  i t = λ σ vsᴿ → sim (vsᴿ >>ᴿ (thᴿ σ <$>ᴿ ρᴿ)) t
\end{code}
