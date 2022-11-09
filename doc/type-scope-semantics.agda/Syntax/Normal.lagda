\begin{code}

{-# OPTIONS --safe #-}

open import Syntax.Type

module Syntax.Normal (NoEta : Type → Set) where

open import Data.Environment
open import Data.Relation
open import Syntax.Calculus
open import Data.List.Base using (List; []; _∷_)
open import Syntax.Type
open import Data.Var
open import Function
open import Relation.Unary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Extra

private

  variable

    σ τ : Type
    Γ Δ Θ : List Type


\end{code}
%<*normal>
\begin{code}
mutual

  data Ne : Type ─Scoped where
    `var   : ∀[ Var σ ⇒ Ne σ ]
    `app   : ∀[ Ne (σ `→ τ) ⇒ Nf σ ⇒ Ne τ ]
    `ifte  : ∀[ Ne `Bool ⇒ Nf σ ⇒ Nf σ ⇒ Ne σ ]

  data Nf : Type ─Scoped where
    `neu     : NoEta σ → ∀[ Ne σ ⇒ Nf σ ]
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

th^Ne : Thinnable (Ne σ)
th^Nf : Thinnable (Nf σ)

th^Ne (`var v)      ρ = `var (th^Var v ρ)
th^Ne (`app f t)    ρ = `app (th^Ne f ρ) (th^Nf t ρ)
th^Ne (`ifte b l r) ρ = `ifte (th^Ne b ρ) (th^Nf l ρ) (th^Nf r ρ)

th^Nf (`neu ne t) ρ = `neu ne (th^Ne t ρ)
th^Nf `one        ρ = `one
th^Nf `tt         ρ = `tt
th^Nf `ff         ρ = `ff
th^Nf (`lam b)    ρ = `lam (th^Nf b (select ρ extend ∙ z))

th^Ne-id : ∀ (t : Ne σ Γ) {ρ} → All Eqᴿ Γ ρ (pack id) → th^Ne t ρ ≡ t
th^Nf-id : ∀ (t : Nf σ Γ) {ρ} → All Eqᴿ Γ ρ (pack id) → th^Nf t ρ ≡ t

th^Ne-id (`var v)      ρᴿ = cong `var (lookupᴿ ρᴿ v)
th^Ne-id (`app f t)    ρᴿ = cong₂ `app (th^Ne-id f ρᴿ) (th^Nf-id t ρᴿ)
th^Ne-id (`ifte b l r) ρᴿ = cong₃ `ifte (th^Ne-id b ρᴿ) (th^Nf-id l ρᴿ) (th^Nf-id r ρᴿ)

th^Nf-id (`neu ne t) ρᴿ = cong (`neu ne) (th^Ne-id t ρᴿ)
th^Nf-id `one        ρᴿ = refl
th^Nf-id `tt         ρᴿ = refl
th^Nf-id `ff         ρᴿ = refl
th^Nf-id (`lam b)    ρᴿ = cong `lam $ th^Nf-id b $ packᴿ λ where
  z     → refl
  (s v) → cong s (lookupᴿ ρᴿ v)

th^Ne-compose :
  (t : Ne σ Γ) {ρ₁ : Thinning Γ Δ} {ρ₂ : Thinning Δ Θ} {ρ₃ : Thinning Γ Θ} →
  All Eqᴿ Γ (select ρ₁ ρ₂) ρ₃ → th^Ne (th^Ne t ρ₁) ρ₂ ≡ th^Ne t ρ₃
th^Nf-compose :
  (t : Nf σ Γ) {ρ₁ : Thinning Γ Δ} {ρ₂ : Thinning Δ Θ} {ρ₃ : Thinning Γ Θ} →
  All Eqᴿ Γ (select ρ₁ ρ₂) ρ₃ → th^Nf (th^Nf t ρ₁) ρ₂ ≡ th^Nf t ρ₃

th^Ne-compose (`var v)      ρᴿ = cong `var (lookupᴿ ρᴿ v)
th^Ne-compose (`app f t)    ρᴿ = cong₂ `app (th^Ne-compose f ρᴿ) (th^Nf-compose t ρᴿ)
th^Ne-compose (`ifte b l r) ρᴿ =
  cong₃ `ifte (th^Ne-compose b ρᴿ) (th^Nf-compose l ρᴿ) (th^Nf-compose r ρᴿ)

th^Nf-compose (`neu ne t) ρᴿ = cong (`neu ne) (th^Ne-compose t ρᴿ)
th^Nf-compose `one        ρᴿ = refl
th^Nf-compose `tt         ρᴿ = refl
th^Nf-compose `ff         ρᴿ = refl
th^Nf-compose (`lam b)    ρᴿ = cong `lam $ th^Nf-compose b $ packᴿ λ where
  z     → refl
  (s v) → cong s (lookupᴿ ρᴿ v)

\end{code}
