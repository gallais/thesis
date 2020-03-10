\begin{code}

module Semantics.NormalisationByEvaluation.Specification where

open import Semantics.Specification
open import Data.List.Base
open import Data.Var
open import Data.Environment
open import Syntax.Type
open import Syntax.Calculus
open import Relation.Unary
open import Function.Base

private
  variable
    σ : Type
    Γ Δ : List Type

\end{code}
%<*recnbe>
\begin{code}
record NBE (Model : Type ─Scoped) (Nf : Type ─Scoped) : Set₁ where
  field  Sem    : Semantics Model Model
         embed  : ∀[ Var σ ⇒ Model σ ]
         reify  : ∀[ Model σ ⇒ Nf σ ]
\end{code}
%</recnbe>
\begin{code}

\end{code}
%<*eval>
\begin{code}
  eval : ∀[ Term σ ⇒ Model σ ]
  eval = semantics Sem (pack embed)
\end{code}
%</eval>
\begin{code}

\end{code}
%<*nbe>
\begin{code}
  nbe : ∀[ Term σ ⇒ Nf σ ]
  nbe = reify ∘ eval
\end{code}
%</nbe>
%<*test>
\begin{code}
  test : Nf (`Bool `→ `Unit `→ `Unit) []
  test = nbe (`lam (`lam (`app (`lam (`var z))
                               (`ifte (`var (s z)) `one (`var z)))))
\end{code}
%</test>
