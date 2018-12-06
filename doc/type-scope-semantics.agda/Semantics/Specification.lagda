\begin{code}
module Semantics.Specification where

open import Syntax.Type
open import Syntax.Calculus
open import Data.Var
open import Data.Environment hiding (Kripke)
open import Data.List using (List; []; _∷_)
open import Relation.Unary

private

  variable
    σ τ : Type
    Γ Δ : List Type
    𝓥 𝓒 : Type ─Scoped

\end{code}
%<*comp>
\begin{code}
_─Comp : List Type → Type ─Scoped → List Type → Set
(Γ ─Comp) 𝓒 Δ = ∀ {σ} → Term σ Γ → 𝓒 σ Δ
\end{code}
%</comp>

%<*kripke>
\begin{code}
Kripke : (𝓥 𝓒 : Type ─Scoped) → Type → Type → List Type → Set
Kripke 𝓥 𝓒 σ τ Γ = ∀[ Thinning Γ ⇒ 𝓥 σ ⇒ 𝓒 τ ]
\end{code}
%</kripke>
%<*recsem>
\begin{code}
record Semantics (𝓥 𝓒 : Type ─Scoped) : Set where
\end{code}
%</recsem>
\begin{code}
  field
\end{code}
%<*thV>
\begin{code}
    th^𝓥   :  Thinnable (𝓥 σ)
\end{code}
%</thV>
%<*var>
\begin{code}
    var    :  ∀[ 𝓥 σ ⇒ 𝓒 σ ]
\end{code}
%</var>
%<*lam>
\begin{code}
    lam    :  ∀[ □ (𝓥 σ ⇒ 𝓒 τ) ⇒ 𝓒 (σ `→ τ) ]
\end{code}
%</lam>
%<*cons>
\begin{code}
    app    :  ∀[ 𝓒 (σ `→ τ) ⇒ 𝓒 σ ⇒ 𝓒 τ ]
    one    :  ∀[ 𝓒 `Unit ]
    tt     :  ∀[ 𝓒 `Bool ]
    ff     :  ∀[ 𝓒 `Bool ]
    ifte   :  ∀[ 𝓒 `Bool ⇒ 𝓒 σ ⇒ 𝓒 σ ⇒ 𝓒 σ ]
\end{code}
%</cons>
\begin{code}
Evaluation : (𝓥 𝓒 : Type ─Scoped) → Set
Evaluation 𝓥 𝓒 = ∀ {Γ Δ} → (Γ ─Env) 𝓥 Δ → (Γ ─Comp) 𝓒 Δ

Evaluation' : (𝓒 :  Type ─Scoped) → Set
Evaluation' 𝓒 = ∀ {Γ} → (Γ ─Comp) 𝓒 Γ

\end{code}
%<*fundamental>
\begin{code}
module Fundamental (𝓢 : Semantics 𝓥 𝓒) where
  open Semantics 𝓢

  lemma : (Γ ─Env) 𝓥 Δ → (Γ ─Comp) 𝓒 Δ
  lemma ρ (`var v)       = var (lookup ρ v)
  lemma ρ (`app t u)     = app (lemma ρ t) (lemma ρ u)
  lemma ρ (`lam t)       = lam (λ re u → lemma (th^Env th^𝓥 ρ re ∙ u) t)
  lemma ρ `one           = one
  lemma ρ `tt            = tt
  lemma ρ `ff            = ff
  lemma ρ (`ifte b l r)  = ifte (lemma ρ b) (lemma ρ l) (lemma ρ r)
\end{code}
%</fundamental>
\begin{code}
eval = Fundamental.lemma
\end{code}
