\begin{code}
module Data.Relation {I : Set} where

open import Size
open import Data.Sum
open import Data.List.Base hiding (lookup ; [_])

open import Data.Var hiding (_<$>_)
open import Data.Environment
open import Generic.Syntax
open import Relation.Unary hiding (U)
open import Agda.Builtin.Equality
open import Function


record Rel (T U : I ─Scoped) : Set₁ where
  constructor mkRel
  field rel : ∀ i → ∀[ T i ⇒ U i ⇒ const Set ]
open Rel public

record All {T U} {Δ} (𝓡 : Rel T U) Γ (ρ₁ : (Γ ─Env) T Δ) (ρ₂ : (Γ ─Env) U Δ) : Set where
  constructor packᴿ
  field lookupᴿ : ∀ {i} k → rel 𝓡 i (lookup ρ₁ k) (lookup ρ₂ k)
open All public

module _ {T U : I ─Scoped} {𝓡 : Rel T U} where

  private
    variable
      σ : I
      Γ Δ : List I
      ρᵀ σᵀ : (Γ ─Env) T Δ
      ρᵁ σᵁ : (Γ ─Env) U Δ
      vᵀ : T σ Γ
      vᵁ : U σ Γ
      fᵀ : ∀ {i} → T i Γ → T i Δ
      fᵁ : ∀ {i} → U i Γ → U i Δ

  εᴿ : All 𝓡 [] ρᵀ ρᵁ
  lookupᴿ εᴿ ()

  infixl 20 _∙ᴿ_
  _∙ᴿ_ :  All 𝓡 Γ ρᵀ ρᵁ → rel 𝓡 σ vᵀ vᵁ → All 𝓡 (σ ∷ Γ) (ρᵀ ∙ vᵀ) (ρᵁ ∙ vᵁ)
  lookupᴿ (ρ ∙ᴿ v) z      = v
  lookupᴿ (ρ ∙ᴿ v) (s k)  = lookupᴿ ρ k

  _>>ᴿ_ :  All 𝓡 Γ ρᵀ ρᵁ → All 𝓡 Δ σᵀ σᵁ →
           All 𝓡 (Γ ++  Δ) (ρᵀ >> σᵀ) (ρᵁ >> σᵁ)
  lookupᴿ (_>>ᴿ_ {Γ} ρᴿ σᴿ) k with split Γ k
  ... | inj₁ k₁ = lookupᴿ ρᴿ k₁
  ... | inj₂ k₂ = lookupᴿ σᴿ k₂

  _<$>ᴿ_ : (∀ {i t u} → rel 𝓡 i t u → rel 𝓡 i (fᵀ t) (fᵁ u)) →
           All 𝓡 Γ ρᵀ ρᵁ → All 𝓡 Γ (fᵀ <$> ρᵀ) (fᵁ <$> ρᵁ)
  lookupᴿ (F <$>ᴿ ρ) k = F (lookupᴿ ρ k)

module _ {A : I ─Scoped} where

  private
    variable
      Γ Δ : List I
      ρ : (Γ ─Env) A Δ

  Eqᴿ : Rel A A
  rel Eqᴿ i = _≡_

  reflᴿ : All Eqᴿ Γ ρ ρ
  lookupᴿ reflᴿ k = refl

module _ {A B : I ─Scoped} where

  open import Relation.Binary.HeterogeneousEquality.Core

  HEqᴿ : Rel A B
  rel HEqᴿ i = λ a b → a ≅ b

module _ {d : Desc I} where

 VarTmᴿ : Rel Var (Tm d ∞)
 rel VarTmᴿ i v t = `var v ≡ t
\end{code}
