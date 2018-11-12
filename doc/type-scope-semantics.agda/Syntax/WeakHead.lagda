\begin{code}
module Syntax.WeakHead where

open import Syntax.Type
open import Syntax.Calculus
open import Semantics.Syntactic.Instances

open import Data.Var
open import Data.Environment
open import Data.List.Base using (List; []; _∷_)

open import Relation.Unary

private

  variable

    σ τ : Type
    Γ Δ : List Type

\end{code}
%<*weakhead>
\begin{code}
mutual

  data WHNE : Type ─Scoped where
    `var   : ∀[ Var σ ⇒ WHNE σ ]
    `app   : ∀[ WHNE (σ `→ τ) ⇒ Term σ ⇒ WHNE τ ]
    `ifte  : ∀[ WHNE `Bool ⇒ Term σ ⇒ Term σ ⇒ WHNE σ ]

  data WHNF : Type ─Scoped where
    `lam     : ∀[ (σ ∷_) ⊢ Term τ ⇒ WHNF (σ `→ τ) ]
    `one     : ∀[ WHNF `Unit ]
    `tt `ff  : ∀[ WHNF `Bool ]
    `whne    : ∀[ WHNE σ ⇒ WHNF σ ]
\end{code}
%</weakhead>
%<*thweakhead>
\begin{code}
th^WHNE : Thinnable (WHNE σ)
th^WHNE (`var v)       ρ = `var (lookup ρ v)
th^WHNE (`app f t)     ρ = `app (th^WHNE f ρ) (th^Term t ρ)
th^WHNE (`ifte b l r)  ρ = `ifte (th^WHNE b ρ) (th^Term l ρ) (th^Term r ρ)

th^WHNF : Thinnable (WHNF σ)
th^WHNF (`lam b)   ρ = `lam (th^Term b (th^Env th^Var ρ extend ∙ z))
th^WHNF `one       ρ = `one
th^WHNF `tt        ρ = `tt
th^WHNF `ff        ρ = `ff
th^WHNF (`whne t)  ρ = `whne (th^WHNE t ρ)
\end{code}
%</thweakhead>
%<*erase>
\begin{code}
erase^WHNE : ∀[ WHNE σ ⇒ Term σ ]
erase^WHNE (`var v)       = `var v
erase^WHNE (`app f t)     = `app (erase^WHNE f) t
erase^WHNE (`ifte b l r)  = `ifte (erase^WHNE b) l r

erase^WHNF : ∀[ WHNF σ ⇒ Term σ ]
erase^WHNF (`lam b)   = `lam b
erase^WHNF `one       = `one
erase^WHNF `tt        = `tt
erase^WHNF `ff        = `ff
erase^WHNF (`whne t)  = erase^WHNE t
\end{code}
%</erase>
