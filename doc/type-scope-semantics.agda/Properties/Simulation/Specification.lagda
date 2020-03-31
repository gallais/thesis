\begin{code}
open import Syntax.Type
open import Data.Var

module Properties.Simulation.Specification {𝓥ᴬ 𝓒ᴬ 𝓥ᴮ 𝓒ᴮ : Type ─Scoped} where

open import Data.Environment
open import Data.List.Base using (List; []; _∷_)
open import Data.Relation
open import Syntax.Type
open import Syntax.Calculus
open import Semantics.Specification
open import Function renaming (_$′_ to _$_) using ()

private
  variable
    σ τ : Type
    Γ Δ Θ : List Type
    ρᴬ : (Γ ─Env) 𝓥ᴬ Δ
    ρᴮ : (Γ ─Env) 𝓥ᴮ Δ
    vᴬ : 𝓥ᴬ σ Γ
    vᴮ : 𝓥ᴮ σ Γ

\end{code}
%<*simulation>
\begin{code}
record Simulation  (𝓢ᴬ : Semantics 𝓥ᴬ 𝓒ᴬ) (𝓢ᴮ : Semantics 𝓥ᴮ 𝓒ᴮ)
                   (𝓥ᴿ : Rel 𝓥ᴬ 𝓥ᴮ) (𝓒ᴿ : Rel 𝓒ᴬ 𝓒ᴮ) : Set where
\end{code}
%</simulation>
\begin{code}
  module 𝓢ᴬ = Semantics 𝓢ᴬ
  module 𝓢ᴮ = Semantics 𝓢ᴮ
\end{code}
%<*crel>
\begin{code}
  𝓡 : ∀ σ → (Γ ─Env) 𝓥ᴬ Δ → (Γ ─Env) 𝓥ᴮ Δ → Term σ Γ → Set
  𝓡 σ ρᴬ ρᴮ t = rel 𝓒ᴿ σ (semantics 𝓢ᴬ ρᴬ t) (semantics 𝓢ᴮ ρᴮ t)
\end{code}
%</crel>
\begin{code}
  open Rel 𝓥ᴿ renaming (rel to 𝓡ⱽ)
\end{code}
%<*rkripke>
\begin{code}
  Kripkeᴿ :  ∀ {Γ Δ} σ τ → (Γ ─Env) 𝓥ᴬ Δ → (Γ ─Env) 𝓥ᴮ Δ →
             Term τ (σ ∷ Γ) → Set
  Kripkeᴿ {Γ} {Δ} σ τ ρᴬ ρᴮ b =
    ∀ {Θ} (ρ : Thinning Δ Θ) {uᴬ uᴮ} → 𝓡ⱽ σ uᴬ uᴮ →
    𝓡 τ (th^Env 𝓢ᴬ.th^𝓥 ρᴬ ρ ∙ uᴬ) (th^Env 𝓢ᴮ.th^𝓥 ρᴮ ρ ∙ uᴮ) b
\end{code}
%</rkripke>
\begin{code}
  field
\end{code}
%<*thV>
\begin{code}
    th^𝓥ᴿ  : (ρ : Thinning Δ Θ) → 𝓡ⱽ σ vᴬ vᴮ → 𝓡ⱽ σ (𝓢ᴬ.th^𝓥 vᴬ ρ) (𝓢ᴮ.th^𝓥 vᴮ ρ)
\end{code}
%</thV>
%<*var>
\begin{code}
    varᴿ   :  All 𝓥ᴿ Γ ρᴬ ρᴮ → (v : Var σ Γ) → 𝓡 σ ρᴬ ρᴮ (`var v)
\end{code}
%</var>
%<*lam>
\begin{code}
    lamᴿ   :  All 𝓥ᴿ Γ ρᴬ ρᴮ → ∀ b → Kripkeᴿ σ τ ρᴬ ρᴮ b → 𝓡 (σ `→ τ) ρᴬ ρᴮ (`lam b)
\end{code}
%</lam>
%<*struct>
\begin{code}
    appᴿ :  All 𝓥ᴿ Γ ρᴬ ρᴮ →
            ∀ f t → 𝓡 (σ `→ τ) ρᴬ ρᴮ f → 𝓡 σ ρᴬ ρᴮ t →
            𝓡 τ ρᴬ ρᴮ (`app f t)
    ifteᴿ : All 𝓥ᴿ Γ ρᴬ ρᴮ →
            ∀ b l r → 𝓡 `Bool ρᴬ ρᴮ b → 𝓡 σ ρᴬ ρᴮ l → 𝓡 σ ρᴬ ρᴮ r →
            𝓡 σ ρᴬ ρᴮ (`ifte b l r)
\end{code}
%</struct>
%<*base>
\begin{code}
    oneᴿ  : All 𝓥ᴿ Γ ρᴬ ρᴮ → 𝓡 `Unit ρᴬ ρᴮ `one
    ttᴿ   : All 𝓥ᴿ Γ ρᴬ ρᴮ → 𝓡 `Bool ρᴬ ρᴮ `tt
    ffᴿ   : All 𝓥ᴿ Γ ρᴬ ρᴮ → 𝓡 `Bool ρᴬ ρᴮ `ff
\end{code}
%</base>
\begin{code}


private
  variable
    𝓢ᴬ : Semantics 𝓥ᴬ 𝓒ᴬ
    𝓢ᴮ : Semantics 𝓥ᴮ 𝓒ᴮ
    𝓥ᴿ : Rel 𝓥ᴬ 𝓥ᴮ
    𝓒ᴿ : Rel 𝓒ᴬ 𝓒ᴮ

module _ (𝓢ᴿ : Simulation 𝓢ᴬ 𝓢ᴮ 𝓥ᴿ 𝓒ᴿ) where

 open Simulation 𝓢ᴿ
\end{code}
%<*fundamental:type>
\begin{code}
 simulation : All 𝓥ᴿ Γ ρᴬ ρᴮ → ∀ t → 𝓡 σ ρᴬ ρᴮ t
\end{code}
%</fundamental:type>
%<*fundamental:var>
\begin{code}
 simulation ρᴿ (`var v)       = varᴿ ρᴿ v
\end{code}
%</fundamental:var>
%<*fundamental:lam>
\begin{code}
 simulation ρᴿ (`lam b)       =  lamᴿ ρᴿ b $ λ ren vᴿ →
                                 simulation ((th^𝓥ᴿ ren <$>ᴿ ρᴿ) ∙ᴿ vᴿ) b
\end{code}
%</fundamental:lam>
%<*fundamental:base>
\begin{code}
 simulation ρᴿ `one           = oneᴿ ρᴿ
 simulation ρᴿ `tt            = ttᴿ ρᴿ
 simulation ρᴿ `ff            = ffᴿ ρᴿ
\end{code}
%</fundamental:base>
%<*fundamental:struct>
\begin{code}
 simulation ρᴿ (`app f t)     = appᴿ ρᴿ f t (simulation ρᴿ f) (simulation ρᴿ t)
 simulation ρᴿ (`ifte b l r)  =
   ifteᴿ ρᴿ b l r (simulation ρᴿ b) (simulation ρᴿ l) (simulation ρᴿ r)
\end{code}
%</fundamental:struct>
