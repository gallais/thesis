\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Syntax.Calculus where

open import Data.Var
open import Syntax.Type
open import Data.List.Base using (List; []; _∷_)
open import Relation.Unary

private
  variable
    σ τ : Type

-- The calculus is defined in a well-scoped and well-typed
-- manner using an inductive family. A term effectively
-- correponds to a derivation in the sequent calculus.

-- Nota Bene: there are TWO proofs of Γ ⊢ `Bool corresponding
-- to true and false respectively.

\end{code}
%<*term>
\begin{code}
data Term : Type ─Scoped where

  `var     :  ∀[ Var σ
              ---------
              ⇒  Term σ ]

  `app     :  ∀[ Term (σ `→ τ) ⇒ Term σ
              ----------------------
              ⇒ Term τ ]

  `lam     :  ∀[ (σ ∷_) ⊢ Term τ
              ---------------
              ⇒ Term (σ `→ τ) ]

  `one     :  ∀[
              ---------
              Term `Unit ]

  `tt      :  ∀[
              ---------
              Term `Bool ]

  `ff      :  ∀[
              ---------
              Term `Bool ]

  `ifte    :  ∀[ Term `Bool ⇒ Term σ ⇒ Term σ
              ----------------------------
              ⇒ Term σ ]
\end{code}
%</term>
