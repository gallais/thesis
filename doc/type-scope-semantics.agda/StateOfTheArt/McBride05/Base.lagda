\begin{code}
module StateOfTheArt.McBride05.Base where

open import Data.List hiding ([_]; lookup)
open import Data.Var hiding (_<$>_)
open import Data.Environment
open import Relation.Unary
open import Function

data Type : Set where
  base : Type
  arr  : Type → Type → Type

private
  variable
    σ τ : Type
    Γ Δ : List Type
\end{code}

%<*stlc>
\begin{code}
data Tm : Type ─Scoped where
  `var  : ∀[ Var σ                ⇒ Tm σ          ]
  `app  : ∀[ Tm (arr σ τ) ⇒ Tm σ  ⇒ Tm τ          ]
  `lam  : ∀[ (σ ∷_) ⊢ Tm τ        ⇒ Tm (arr σ τ)  ]
\end{code}
%</stlc>

\begin{code}

module RenSub where
\end{code}
%<*ren>
\begin{code}
 ren : (Γ ─Env) Var Δ → Tm σ Γ → Tm σ Δ
 ren ρ (`var v)    = `var (lookup ρ v)
 ren ρ (`app f t)  = `app (ren ρ f) (ren ρ t)
 ren ρ (`lam b)    = `lam (ren ρ′ b)
   where ρ′ = (s <$> ρ) ∙ z
\end{code}
%</ren>

%<*sub>
\begin{code}
 sub : (Γ ─Env) Tm Δ → Tm σ Γ → Tm σ Δ
 sub ρ (`var v)    = lookup ρ v
 sub ρ (`app f t)  = `app (sub ρ f) (sub ρ t)
 sub ρ (`lam b)    = `lam (sub ρ′ b)
   where ρ′ = (ren (pack s) <$> ρ) ∙ `var z
\end{code}
%</sub>
