\begin{code}
open import Syntax.Type
open import Data.Var

module Properties.Fusion.Syntactic.Specification  {𝓣ᴬ 𝓣ᴮ 𝓣ᴬᴮ : Type ─Scoped} where

open import Data.Environment
open import Data.List.Base using (List; []; _∷_)
open import Data.Relation hiding (_∙ᴿ_)
open import Syntax.Type
open import Syntax.Calculus
open import Semantics.Specification
open import Semantics.Syntactic.Specification as SynSpec
open import Function renaming (_$′_ to _$_) using (id)
open import Properties.Fusion.Specification
open import Relation.Unary
open import Relation.Binary.PropositionalEquality.Extra

private
  variable
    σ τ : Type
    Γ Δ Θ Ω : List Type
    ρᴬ : (Γ ─Env) 𝓣ᴬ Δ
    ρᴮ : (Δ ─Env) 𝓣ᴮ Θ
    ρᴬᴮ : (Γ ─Env) 𝓣ᴬᴮ Θ
    tᴮ : 𝓣ᴮ σ Γ
    tᴬᴮ : 𝓣ᴬᴮ σ Γ
\end{code}
%<*synfusion>
\begin{code}
record SynFusion
  (Synᴬ : Syntactic 𝓣ᴬ) (Synᴮ : Syntactic 𝓣ᴮ) (Synᴬᴮ : Syntactic 𝓣ᴬᴮ)
  (𝓔ᴿ : ∀ {Γ Δ Θ} → (Γ ─Env) 𝓣ᴬ Δ → (Δ ─Env) 𝓣ᴮ Θ → (Γ ─Env) 𝓣ᴬᴮ Θ → Set)
  (𝓣ᴿ : Rel 𝓣ᴮ 𝓣ᴬᴮ) : Set where
\end{code}
%</synfusion>
\begin{code}
  module Synᴬ = Syntactic Synᴬ
  module Synᴮ = Syntactic Synᴮ
  module Synᴬᴮ = Syntactic Synᴬᴮ
  evalᴬ = Semantics.Specification.semantics (SynSpec.syntactic Synᴬ)
  evalᴮ = Semantics.Specification.semantics (SynSpec.syntactic Synᴮ)
  evalᴬᴮ = Semantics.Specification.semantics (SynSpec.syntactic Synᴬᴮ)
\end{code}
%<*crel>
\begin{code}
  𝓡 :  ∀ σ → (Γ ─Env) 𝓣ᴬ Δ → (Δ ─Env) 𝓣ᴮ Θ → (Γ ─Env) 𝓣ᴬᴮ Θ →
       Term σ Γ → Set
  𝓡 σ ρᴬ ρᴮ ρᴬᴮ t = evalᴮ ρᴮ (evalᴬ ρᴬ t) ≡ evalᴬᴮ ρᴬᴮ t
\end{code}
%</crel>
\begin{code}
  field
\end{code}
%<*thV>
\begin{code}
    _∙ᴿ_    :  𝓔ᴿ ρᴬ ρᴮ ρᴬᴮ → rel 𝓣ᴿ σ tᴮ tᴬᴮ →
               𝓔ᴿ (th^Env Synᴬ.th^𝓣 ρᴬ extend ∙ Synᴬ.zro) (ρᴮ ∙ tᴮ) (ρᴬᴮ ∙ tᴬᴮ)
    th^𝓔ᴿ  :  𝓔ᴿ ρᴬ ρᴮ ρᴬᴮ → (ρ : Thinning Θ Ω) →
              𝓔ᴿ ρᴬ (th^Env Synᴮ.th^𝓣 ρᴮ ρ) (th^Env Synᴬᴮ.th^𝓣 ρᴬᴮ ρ)
\end{code}
%</thV>
%<*var>
\begin{code}
    varᴿ : 𝓔ᴿ ρᴬ ρᴮ ρᴬᴮ → (v : Var σ Γ) → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ (`var v)
\end{code}
%</var>
%<*zro>
\begin{code}
    zroᴿ : rel 𝓣ᴿ σ {σ ∷ Γ} Synᴮ.zro Synᴬᴮ.zro
\end{code}
%</zro>
\begin{code}

private
  variable
    Synᴬ : Syntactic 𝓣ᴬ
    Synᴮ : Syntactic 𝓣ᴮ
    Synᴬᴮ : Syntactic 𝓣ᴬᴮ
    𝓔ᴿ : ∀ {Γ Δ Θ} → (Γ ─Env) 𝓣ᴬ Δ → (Δ ─Env) 𝓣ᴮ Θ → (Γ ─Env) 𝓣ᴬᴮ Θ → Set
    𝓣ᴿ : Rel 𝓣ᴮ 𝓣ᴬᴮ

fromSyn = SynSpec.syntactic

\end{code}
%<*fundamental>
\begin{code}
module Fundamental (𝓕 : SynFusion Synᴬ Synᴮ Synᴬᴮ 𝓔ᴿ 𝓣ᴿ) where

  open SynFusion 𝓕

  lemma : Fusion (fromSyn Synᴬ) (fromSyn Synᴮ) (fromSyn Synᴬᴮ) 𝓔ᴿ 𝓣ᴿ Eqᴿ
  lemma .Fusion.reifyᴬ  = id
  lemma .Fusion.var0ᴬ   = Synᴬ.zro
  lemma .Fusion._∙ᴿ_    = _∙ᴿ_
  lemma .Fusion.th^𝓔ᴿ   = th^𝓔ᴿ
  lemma .Fusion.varᴿ    = varᴿ
  lemma .Fusion.oneᴿ    = λ ρᴿ → refl
  lemma .Fusion.ttᴿ     = λ ρᴿ → refl
  lemma .Fusion.ffᴿ     = λ ρᴿ → refl
  lemma .Fusion.appᴿ    = λ ρᴿ f t → cong₂ `app
  lemma .Fusion.ifteᴿ   = λ ρᴿ b l r → cong₃ `ifte
  lemma .Fusion.lamᴿ    = λ ρᴿ b bᴿ → cong `lam (bᴿ extend zroᴿ)
\end{code}
%</fundamental>
