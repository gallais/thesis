\begin{code}
module Syntax.MoggiML.Type where

open import Data.Product
open import Relation.Binary.PropositionalEquality

infixr 20 _`→#_ #_
\end{code}
%<*ctype>
\begin{code}
data CType : Set where
  `Unit  : CType
  `Bool  : CType
  _`→#_  : (σ τ : CType) → CType
  #_     : CType → CType
\end{code}
%</ctype>
\begin{code}
private

  variable

    σ τ σ₁ τ₁ σ₂ τ₂ : CType

`→#-inj : (σ₁ `→# τ₁) ≡ (σ₂ `→# τ₂) → σ₁ ≡ σ₂ × τ₁ ≡ τ₂
`→#-inj refl = refl , refl

#-inj : # σ ≡ # τ → σ ≡ τ
#-inj refl = refl
\end{code}
