\begin{code}
{-# OPTIONS --sized-types #-}
module Data.Environment.Sized where

open import Size
open import Data.List.Base using (List; _++_)
open import Data.Var
open import Data.Environment
open import Function.Base using (const; _∘_)

open import Relation.Unary using (IUniversal; _⇒_)
open import Relation.Binary.PropositionalEquality as PEq hiding ([_])

private

  variable
    I A : Set
    size : Size
    i j k l σ : I
    S T U : List I → Set
    𝓥 𝓦 𝓒 : I ─Scoped
    Γ Δ Θ : List I
    F : Set → Set


-- stack-based environment
infix 4 _⊣_,,_

data SEnv (𝓥 : I ─Scoped) : Size → (Γ Δ : List I) → Set where
  [_]    : ∀{Γ} → ∀[ (Γ ─Env) 𝓥 ⇒ SEnv 𝓥 (↑ size) Γ ]
  _⊣_,,_ : ∀ Γ₂ {Γ₁} → ∀[ (Γ₂ ─Env) 𝓥 ⇒ ◇ (SEnv 𝓥 size Γ₁) ⇒ SEnv 𝓥 (↑ size) (Γ₂ ++ Γ₁) ]

infix 3 _─◇Env
_─◇Env : (Γ : List I) (𝓥 : I ─Scoped) (Δ : List I) → Set
(Γ ─◇Env) 𝓥 Δ = SEnv 𝓥 _ Γ Δ

slookup : SEnv 𝓥 size Γ Δ → Var σ Γ → ◇ (𝓥 σ) Δ
slookup [ ρ ]           k = DI.pure (lookup ρ k)
slookup (Γ ⊣ ρ₂ ,, ◇ρ₁) k with split Γ k
... | inj₁ kˡ = DI.pure (lookup ρ₂ kˡ)
... | inj₂ kʳ = ◇ρ₁ DI.>>= λ ρ₁ → slookup ρ₁ kʳ
\end{code}
