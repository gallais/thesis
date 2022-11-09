\begin{code}
{-# OPTIONS --safe #-}

module Semantics.Syntactic.Instances where

open import Data.List.Base using (List; []; _∷_)
open import Data.Var hiding (_<$>_)
open import Data.Environment
open import Syntax.Type
open import Syntax.Calculus
open import Semantics.Specification
open import Semantics.Syntactic.Specification
open import Relation.Unary
open import Function

private
  variable
   Γ Δ : List Type
   σ τ : Type

open Syntactic

-- We are, once more, using copatterns to prevent too much unfolding.

\end{code}
%<*synren>
\begin{code}
Syn^Ren : Syntactic Var
Syn^Ren .zro   = z
Syn^Ren .th^𝓣  = th^Var
Syn^Ren .var   = `var
\end{code}
%</synren>
%<*ren>
\begin{code}
Renaming : Semantics Var Term
Renaming = syntactic Syn^Ren

th^Term : Thinnable (Term σ)
th^Term t ρ = semantics Renaming ρ t
\end{code}
%</ren>
\begin{code}
ren : Thinning Γ Δ → Term σ Γ → Term σ Δ
ren ρ t = th^Term t ρ
\end{code}
%<*synsub>
\begin{code}
Syn^Sub : Syntactic Term
Syn^Sub .zro   = `var z
Syn^Sub .th^𝓣  = th^Term
Syn^Sub .var   = id
\end{code}
%</synsub>
%<*sub>
\begin{code}
Substitution : Semantics Term Term
Substitution = syntactic Syn^Sub

sub : (Γ ─Env) Term Δ → Term σ Γ → Term σ Δ
sub ρ t = semantics Substitution ρ t
\end{code}
%</sub>
%<*eta>
\begin{code}
eta : ∀[ Term (σ `→ τ) ⇒ Term (σ `→ τ) ]
eta t = `lam (`app (th^Term t extend) (`var z))
\end{code}
%</eta>
%<*betared>
\begin{code}
_⟨_/0⟩ : ∀[ (σ ∷_) ⊢ Term τ ⇒ Term σ ⇒ Term τ ]
t ⟨ u /0⟩ = sub ((`var <$> identity) ∙ u) t
\end{code}
%</betared>
