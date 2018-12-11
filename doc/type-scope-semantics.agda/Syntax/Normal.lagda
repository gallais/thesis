\begin{code}
open import Syntax.Type

module Syntax.Normal (Eta? : Type → Set) where

open import Syntax.Calculus
open import Data.List.Base using (List; []; _∷_)
open import Syntax.Type
open import Data.Var
open import Relation.Unary
open import Relation.Binary.PropositionalEquality

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
\begin{code}
`neu-injective : ∀ {p q} {t u : Ne σ Γ} → `neu p t ≡ `neu q u → t ≡ u
`neu-injective refl = refl

erase^Ne : ∀[ Ne σ ⇒ Term σ ]
erase^Nf : ∀[ Nf σ ⇒ Term σ ]

erase^Ne (`var v)       = `var v
erase^Ne (`app f t)     = `app (erase^Ne f) (erase^Nf t)
erase^Ne (`ifte b l r)  = `ifte (erase^Ne b) (erase^Nf l) (erase^Nf r)

erase^Nf (`neu _ t) = erase^Ne t
erase^Nf `one       = `one
erase^Nf `tt        = `tt
erase^Nf `ff        = `ff
erase^Nf (`lam b)   = `lam (erase^Nf b)
\end{code}
