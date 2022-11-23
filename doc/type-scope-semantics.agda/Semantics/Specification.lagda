\begin{code}
{-# OPTIONS --safe --sized-types #-}

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
%<*wholerecsem>
%<*recsem>
\begin{code}
record Semantics (𝓥 𝓒 : Type ─Scoped) : Set where
\end{code}
%</recsem>
\begin{code}
  field
\end{code}
%<*recfields>
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
%<*app>
\begin{code}
    app    :  ∀[ 𝓒 (σ `→ τ) ⇒ 𝓒 σ ⇒ 𝓒 τ ]
\end{code}
%</app>
%<*one>
\begin{code}
    one    :  ∀[ 𝓒 `Unit ]
\end{code}
%</one>
%<*bool>
\begin{code}
    tt     :  ∀[ 𝓒 `Bool ]
    ff     :  ∀[ 𝓒 `Bool ]
\end{code}
%</bool>
%<*ifte>
\begin{code}
    ifte   :  ∀[ 𝓒 `Bool ⇒ 𝓒 σ ⇒ 𝓒 σ ⇒ 𝓒 σ ]
\end{code}
%</ifte>
%</recfields>
%</wholerecsem>
\begin{code}
Evaluation : (𝓥 𝓒 : Type ─Scoped) → Set
Evaluation 𝓥 𝓒 = ∀ {Γ Δ} → (Γ ─Env) 𝓥 Δ → (Γ ─Comp) 𝓒 Δ

Evaluation' : (𝓒 :  Type ─Scoped) → Set
Evaluation' 𝓒 = ∀ {Γ} → (Γ ─Comp) 𝓒 Γ

\end{code}
%<*fundamental>
%<*fundamentalheader>
\begin{code}
module _ (𝓢 : Semantics 𝓥 𝓒) where
  open Semantics 𝓢
\end{code}
%</fundamentalheader>
%<*fundamentalbody>
%<*semantics-type>
\begin{code}
  semantics : (Γ ─Env) 𝓥 Δ → (Γ ─Comp) 𝓒 Δ
\end{code}
%</semantics-type>
%<*semantics-var>
\begin{code}
  semantics ρ (`var v)       = var (lookup ρ v)
\end{code}
%</semantics-var>
%<*semantics-app>
\begin{code}
  semantics ρ (`app t u)     = app (semantics ρ t) (semantics ρ u)
\end{code}
%</semantics-app>
%<*semantics-lam>
\begin{code}
  semantics ρ (`lam t)       = lam (λ re u → semantics (th^Env th^𝓥 ρ re ∙ u) t)
\end{code}
%</semantics-lam>
%<*semantics-one>
\begin{code}
  semantics ρ `one           = one
\end{code}
%</semantics-one>
%<*semantics-bool>
\begin{code}
  semantics ρ `tt            = tt
  semantics ρ `ff            = ff
\end{code}
%</semantics-bool>
%<*semantics-ifte>
\begin{code}
  semantics ρ (`ifte b l r)  = ifte (semantics ρ b) (semantics ρ l) (semantics ρ r)
\end{code}
%</semantics-ifte>
%</fundamentalbody>
%</fundamental>
