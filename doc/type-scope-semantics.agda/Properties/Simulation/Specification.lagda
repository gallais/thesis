\begin{code}
open import Syntax.Type
open import Data.Var

module Properties.Simulation.Specification {𝓥ᴬ 𝓒ᴬ 𝓥ᴮ 𝓒ᴮ : Type ─Scoped} where

open import Data.Environment
open import Data.List.Base using (List; []; _∷_)
open import Data.Relation
open import Syntax.Type
open import Syntax.Calculus
open import Semantics.Specification hiding (module Fundamental)

private
  variable
    σ τ : Type
    Γ Δ Θ : List Type
    ρᴬ : (Γ ─Env) 𝓥ᴬ Δ
    ρᴮ : (Γ ─Env) 𝓥ᴮ Δ

record Simulation  (𝓢ᴬ : Semantics 𝓥ᴬ 𝓒ᴬ) (𝓢ᴮ : Semantics 𝓥ᴮ 𝓒ᴮ)
                   (𝓥ᴿ : Rel 𝓥ᴬ 𝓥ᴮ) (𝓒ᴿ : Rel 𝓒ᴬ 𝓒ᴮ) : Set where
  module 𝓢ᴬ = Semantics 𝓢ᴬ
  module 𝓢ᴮ = Semantics 𝓢ᴮ
  evalᴬ = Semantics.Specification.Fundamental.lemma 𝓢ᴬ
  evalᴮ = Semantics.Specification.Fundamental.lemma 𝓢ᴮ
  𝓡 : ∀ {Γ Δ} σ → (Γ ─Env) 𝓥ᴬ Δ → (Γ ─Env) 𝓥ᴮ Δ → Term σ Γ → Set
  𝓡 = λ σ ρᴬ ρᴮ t → rel 𝓒ᴿ σ (evalᴬ ρᴬ t) (evalᴮ ρᴮ t)

  field

    th^𝓥ᴿ  :  All 𝓥ᴿ Γ ρᴬ ρᴮ → (ren : Thinning Δ Θ) →
               All 𝓥ᴿ Γ (th^Env 𝓢ᴬ.th^𝓥 ρᴬ ren) (th^Env 𝓢ᴮ.th^𝓥 ρᴮ ren)

    varᴿ   :  All 𝓥ᴿ Γ ρᴬ ρᴮ → (v : Var σ Γ) → 𝓡 σ ρᴬ ρᴮ (`var v)

    lamᴿ   :  All 𝓥ᴿ Γ ρᴬ ρᴮ → ∀ b →
              (∀ {Θ} (ren : Thinning Δ Θ) {uᴬ uᴮ} →
                rel 𝓥ᴿ σ uᴬ uᴮ →
                𝓡 τ (th^Env 𝓢ᴬ.th^𝓥 ρᴬ ren ∙ uᴬ) (th^Env 𝓢ᴮ.th^𝓥 ρᴮ ren ∙ uᴮ) b) →
              𝓡 (σ `→ τ) ρᴬ ρᴮ (`lam b)

    appᴿ :  All 𝓥ᴿ Γ ρᴬ ρᴮ → ∀ f t → 𝓡 (σ `→ τ) ρᴬ ρᴮ f → 𝓡 σ ρᴬ ρᴮ t →
            𝓡 τ ρᴬ ρᴮ (`app f t)

    oneᴿ  : All 𝓥ᴿ Γ ρᴬ ρᴮ → 𝓡 `Unit ρᴬ ρᴮ `one
    ttᴿ   : All 𝓥ᴿ Γ ρᴬ ρᴮ → 𝓡 `Bool ρᴬ ρᴮ `tt
    ffᴿ   : All 𝓥ᴿ Γ ρᴬ ρᴮ → 𝓡 `Bool ρᴬ ρᴮ `ff

    ifteᴿ : All 𝓥ᴿ Γ ρᴬ ρᴮ → ∀ b l r → 𝓡 `Bool ρᴬ ρᴮ b → 𝓡 σ ρᴬ ρᴮ l → 𝓡 σ ρᴬ ρᴮ r →
            𝓡 σ ρᴬ ρᴮ (`ifte b l r)


module Fundamental
  {𝓢ᴬ : Semantics 𝓥ᴬ 𝓒ᴬ} {𝓢ᴮ : Semantics 𝓥ᴮ 𝓒ᴮ}
  {𝓥ᴿ : Rel 𝓥ᴬ 𝓥ᴮ} {𝓒ᴿ : Rel 𝓒ᴬ 𝓒ᴮ}
  (𝓢ᴿ : Simulation 𝓢ᴬ 𝓢ᴮ 𝓥ᴿ 𝓒ᴿ)
  where

  open Simulation 𝓢ᴿ
  eval = Semantics.Specification.Fundamental.lemma

  lemma : All 𝓥ᴿ Γ ρᴬ ρᴮ → ∀ t → 𝓡 σ ρᴬ ρᴮ t
  lemma ρᴿ (`var v)       = varᴿ ρᴿ v
  lemma ρᴿ (`app f t)     = appᴿ ρᴿ f t (lemma ρᴿ f) (lemma ρᴿ t)
  lemma ρᴿ (`lam b)       = lamᴿ ρᴿ b λ ren uᴿ → lemma (th^𝓥ᴿ ρᴿ ren ∙ᴿ uᴿ) b
  lemma ρᴿ `one           = oneᴿ ρᴿ
  lemma ρᴿ `tt            = ttᴿ ρᴿ
  lemma ρᴿ `ff            = ffᴿ ρᴿ
  lemma ρᴿ (`ifte b l r)  = ifteᴿ ρᴿ b l r (lemma ρᴿ b) (lemma ρᴿ l) (lemma ρᴿ r)

\end{code}
