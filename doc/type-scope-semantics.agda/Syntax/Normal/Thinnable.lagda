\begin{code}
module Syntax.Normal.Thinnable where

open import Data.List.Base using (List; []; _∷_)
open import Syntax.Type
open import Syntax.Normal
open import Data.Var
open import Data.Environment
open import Semantics.Syntactic.Instances
open import Function
open import Relation.Binary.PropositionalEquality

private

  variable

    R : Type → Set
    σ : Type

{-
mutual

  wk^nf-trans′ : 
    ∀ {Γ Δ Θ σ R inc₁ inc₃} {inc₂ : Renaming Δ Θ} →
    `∀[ Equality ] (Env.trans inc₁ inc₂) inc₃ →
    (t : Γ ⊢[ R ]^nf σ) → wk^nf inc₂ (wk^nf inc₁ t) ≡ wk^nf inc₃ t
  wk^nf-trans′ eq (`neu pr t) = cong (`neu pr) $ wk^ne-trans′ eq t
  wk^nf-trans′ eq `⟨⟩         = refl
  wk^nf-trans′ eq `tt         = refl
  wk^nf-trans′ eq `ff         = refl
  wk^nf-trans′ eq (`λ t)      =
    cong `λ $ wk^nf-trans′ ((cong 1+_ ∘ lookup^R eq) ∙^R′ refl) t 

  wk^ne-trans′ : 
    ∀ {Γ Δ Θ σ R inc₁ inc₃} {inc₂ : Renaming Δ Θ} →
    `∀[ Equality ] (Env.trans inc₁ inc₂) inc₃ →
    (t : Γ ⊢[ R ]^ne σ) → wk^ne inc₂ (wk^ne inc₁ t) ≡ wk^ne inc₃ t
  wk^ne-trans′ eq (`var v)      = cong `var $ lookup^R eq v
  wk^ne-trans′ eq (t `$ u)      = cong₂ _`$_ (wk^ne-trans′ eq t) (wk^nf-trans′ eq u)
  wk^ne-trans′ eq (`ifte t l r) =
    cong₂ (uncurry `ifte) (cong₂ _,_ (wk^ne-trans′ eq t) (wk^nf-trans′ eq l))
          (wk^nf-trans′ eq r)

wk^nf-trans :
  ∀ {Γ Δ Θ σ R inc₁} {inc₂ : Renaming Δ Θ} →
  (t : Γ ⊢[ R ]^nf σ) → wk^nf inc₂ (wk^nf inc₁ t) ≡ wk^nf (Env.trans inc₁ inc₂) t  
wk^nf-trans = wk^nf-trans′ $ pack^R $ λ _ → refl

wk^ne-trans :
  ∀ {Γ Δ Θ σ R inc₁} {inc₂ : Renaming Δ Θ} →
  (t : Γ ⊢[ R ]^ne σ) → wk^ne inc₂ (wk^ne inc₁ t) ≡ wk^ne (Env.trans inc₁ inc₂) t  
wk^ne-trans = wk^ne-trans′ $ pack^R $ λ _ → refl
-}
\end{code}
