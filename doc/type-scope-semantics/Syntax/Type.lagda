\begin{code}
module Syntax.Type where

open import Data.Product
open import Relation.Binary.PropositionalEquality

infixr 20 _`→_

\end{code}
%<*type>
\begin{code}
data Type : Set where
  `Unit `Bool : Type
  _`→_  : (σ τ : Type) → Type
\end{code}
%</type>
\begin{code}

`→-inj : {σ₁ τ₁ σ₂ τ₂ : Type} → σ₁ `→ τ₁ ≡ σ₂ `→ τ₂ → σ₁ ≡ σ₂ × τ₁ ≡ τ₂
`→-inj refl = refl , refl
\end{code}
