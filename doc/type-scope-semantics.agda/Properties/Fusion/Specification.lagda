\begin{code}
open import Syntax.Type
open import Data.Var

module Properties.Fusion.Specification  {𝓥ᴬ 𝓒ᴬ 𝓥ᴮ 𝓒ᴮ 𝓥ᴬᴮ 𝓒ᴬᴮ : Type ─Scoped} where

open import Data.Environment
open import Data.List.Base using (List; []; _∷_)
open import Data.Relation hiding (_∙ᴿ_)
open import Syntax.Type
open import Syntax.Calculus
open import Semantics.Specification hiding (module Fundamental)
open import Function renaming (_$′_ to _$_) using ()
open import Relation.Unary

private
  variable
    σ τ : Type
    Γ Δ Θ Ω : List Type
    ρᴬ : (Γ ─Env) 𝓥ᴬ Δ
    ρᴮ : (Δ ─Env) 𝓥ᴮ Θ
    ρᴬᴮ : (Γ ─Env) 𝓥ᴬᴮ Θ
    vᴬᴮ : 𝓥ᴬᴮ σ Γ
    vᴮ : 𝓥ᴮ σ Γ

\end{code}
%<*fusion>
\begin{code}
record Fusion
  (𝓢ᴬ : Semantics 𝓥ᴬ 𝓒ᴬ) (𝓢ᴮ : Semantics 𝓥ᴮ 𝓒ᴮ) (𝓢ᴬᴮ : Semantics 𝓥ᴬᴮ 𝓒ᴬᴮ)
  (𝓔ᴿ : ∀ {Γ Δ Θ} → (Γ ─Env) 𝓥ᴬ Δ → (Δ ─Env) 𝓥ᴮ Θ → (Γ ─Env) 𝓥ᴬᴮ Θ → Set)
  (𝓥ᴿ : Rel 𝓥ᴮ 𝓥ᴬᴮ) (𝓒ᴿ : Rel 𝓒ᴮ 𝓒ᴬᴮ) : Set where
\end{code}
%</fusion>
\begin{code}
  module 𝓢ᴬ = Semantics 𝓢ᴬ
  module 𝓢ᴮ = Semantics 𝓢ᴮ
  module 𝓢ᴬᴮ = Semantics 𝓢ᴬᴮ
  evalᴬ = Semantics.Specification.Fundamental.lemma 𝓢ᴬ
  evalᴮ = Semantics.Specification.Fundamental.lemma 𝓢ᴮ
  evalᴬᴮ = Semantics.Specification.Fundamental.lemma 𝓢ᴬᴮ

  field
\end{code}
%<*reifyvar0>
\begin{code}
    reifyᴬ  : ∀[ 𝓒ᴬ σ ⇒ Term σ ]
    var0ᴬ   : ∀[ (σ ∷_) ⊢ 𝓥ᴬ σ ]
\end{code}
%</reifyvar0>
%<*thV>
\begin{code}
    _∙ᴿ_    :  𝓔ᴿ ρᴬ ρᴮ ρᴬᴮ → rel 𝓥ᴿ σ vᴮ vᴬᴮ →
               𝓔ᴿ (th^Env 𝓢ᴬ.th^𝓥 ρᴬ extend ∙ var0ᴬ) (ρᴮ ∙ vᴮ) (ρᴬᴮ ∙ vᴬᴮ)
    th^𝓔ᴿ  :  𝓔ᴿ ρᴬ ρᴮ ρᴬᴮ → (ρ : Thinning Θ Ω) →
              𝓔ᴿ ρᴬ (th^Env 𝓢ᴮ.th^𝓥 ρᴮ ρ) (th^Env 𝓢ᴬᴮ.th^𝓥 ρᴬᴮ ρ)
\end{code}
%</thV>
%<*crel>
\begin{code}
  𝓡 : ∀ σ → (Γ ─Env) 𝓥ᴬ Δ → (Δ ─Env) 𝓥ᴮ Θ → (Γ ─Env) 𝓥ᴬᴮ Θ → Term σ Γ → Set
  𝓡 σ ρᴬ ρᴮ ρᴬᴮ t = rel 𝓒ᴿ σ (evalᴮ ρᴮ (reifyᴬ (evalᴬ ρᴬ t))) (evalᴬᴮ ρᴬᴮ t)
\end{code}
%</crel>
\begin{code}
  field
\end{code}
%<*var>
\begin{code}
    varᴿ :  𝓔ᴿ ρᴬ ρᴮ ρᴬᴮ → (v : Var σ Γ) → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ (`var v)
\end{code}
%</var>
%<*base>
\begin{code}
    oneᴿ :  𝓔ᴿ ρᴬ ρᴮ ρᴬᴮ → 𝓡 `Unit  ρᴬ ρᴮ ρᴬᴮ `one
    ttᴿ  :  𝓔ᴿ ρᴬ ρᴮ ρᴬᴮ → 𝓡 `Bool  ρᴬ ρᴮ ρᴬᴮ `tt
    ffᴿ  :  𝓔ᴿ ρᴬ ρᴮ ρᴬᴮ → 𝓡 `Bool  ρᴬ ρᴮ ρᴬᴮ `ff
\end{code}
%</base>
%<*struct>
\begin{code}
    appᴿ   :  𝓔ᴿ ρᴬ ρᴮ ρᴬᴮ →
              ∀ f t → 𝓡 (σ `→ τ) ρᴬ ρᴮ ρᴬᴮ f → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ t →
              𝓡 τ  ρᴬ ρᴮ ρᴬᴮ (`app f t)
    ifteᴿ  :  𝓔ᴿ ρᴬ ρᴮ ρᴬᴮ →
              ∀ b l r → 𝓡 `Bool ρᴬ ρᴮ ρᴬᴮ b → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ l → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ r →
              𝓡 σ ρᴬ ρᴮ ρᴬᴮ (`ifte b l r)
\end{code}
%</struct>
%<*lam>
\begin{code}
    lamᴿ :  𝓔ᴿ ρᴬ ρᴮ ρᴬᴮ → ∀ b →
            (∀ {Ω} (ρ : Thinning Θ Ω) {vᴮ vᴬᴮ} → rel 𝓥ᴿ σ vᴮ vᴬᴮ →
               let σᴬ   = th^Env 𝓢ᴬ.th^𝓥 ρᴬ extend ∙ var0ᴬ
                   σᴮ   = th^Env 𝓢ᴮ.th^𝓥 ρᴮ ρ ∙ vᴮ
                   σᴬᴮ  = th^Env 𝓢ᴬᴮ.th^𝓥 ρᴬᴮ ρ ∙ vᴬᴮ
               in 𝓡 τ σᴬ σᴮ σᴬᴮ b) →
            𝓡 (σ `→ τ) ρᴬ ρᴮ ρᴬᴮ (`lam b)
\end{code}
%</lam>
\begin{code}
private
  variable
    𝓢ᴬ : Semantics 𝓥ᴬ 𝓒ᴬ
    𝓢ᴮ : Semantics 𝓥ᴮ 𝓒ᴮ
    𝓢ᴬᴮ : Semantics 𝓥ᴬᴮ 𝓒ᴬᴮ
    𝓔ᴿ : ∀ {Γ Δ Θ} → (Γ ─Env) 𝓥ᴬ Δ → (Δ ─Env) 𝓥ᴮ Θ → (Γ ─Env) 𝓥ᴬᴮ Θ → Set
    𝓥ᴿ : Rel 𝓥ᴮ 𝓥ᴬᴮ
    𝓒ᴿ : Rel 𝓒ᴮ 𝓒ᴬᴮ
\end{code}
%<*fundamental>
\begin{code}
module Fundamental (𝓕 : Fusion 𝓢ᴬ 𝓢ᴮ 𝓢ᴬᴮ 𝓔ᴿ 𝓥ᴿ 𝓒ᴿ) where

  open Fusion 𝓕

  lemma : 𝓔ᴿ ρᴬ ρᴮ ρᴬᴮ → ∀ t → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ t
  lemma ρᴿ (`var v)       = varᴿ ρᴿ v
  lemma ρᴿ (`app f t)     = appᴿ ρᴿ f t (lemma ρᴿ f) (lemma ρᴿ t)
  lemma ρᴿ (`lam b)       = lamᴿ ρᴿ b $ λ ren vᴿ → lemma (th^𝓔ᴿ ρᴿ ren ∙ᴿ vᴿ) b
  lemma ρᴿ `one           = oneᴿ ρᴿ
  lemma ρᴿ `tt            = ttᴿ ρᴿ
  lemma ρᴿ `ff            = ffᴿ ρᴿ
  lemma ρᴿ (`ifte b l r)  = ifteᴿ ρᴿ b l r (lemma ρᴿ b) (lemma ρᴿ l) (lemma ρᴿ r)
\end{code}
%</fundamental>
