\begin{code}
open import Syntax.Type

module Syntax.Normal (Eta? : Type → Set) where

open import Data.List.Base using (List; []; _∷_)
open import Syntax.Type
open import Data.Var
open import Relation.Unary

private

  variable

    σ τ : Type
    Γ Δ : List Type


\end{code}
%<*normal>
\begin{code}
mutual

  data Ne : Type ─Scoped where
    `var   : ∀[ Var σ ⇒ Ne σ ]
    `app   : ∀[ Ne (σ `→ τ) ⇒ Nf σ ⇒ Ne τ ]
    `ifte  : ∀[ Ne `Bool ⇒ Nf σ ⇒ Nf σ ⇒ Ne σ ]

  data Nf : Type ─Scoped where
    `neu     : Eta? σ → ∀[ Ne σ ⇒ Nf σ ]
    `one     : ∀[ Nf `Unit ]
    `tt `ff  : ∀[ Nf `Bool ]
    `lam     : ∀[ (σ ∷_) ⊢ Nf τ ⇒ Nf (σ `→ τ) ]
\end{code}
%</normal>
\end{code}
