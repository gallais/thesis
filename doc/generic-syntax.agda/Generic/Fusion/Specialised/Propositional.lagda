\begin{code}
--------------------------------------------------------------------------------
-- This is the closest one can come to an axiom-free verison of Kaiser, Schäfer,
-- and Stark's observation that our notion of Semantics is intrinsically able to
-- absord any Renaming which may have come before.
--
-- This is used both to replicate Kaiser, Schäfer, and Stark's result in the
-- module Generic.Fusion.Specialised and to make the fusion proofs of renaming
-- with renaming, substitution, and let-elaboration simpler.
--------------------------------------------------------------------------------

module Generic.Fusion.Specialised.Propositional where

open import Relation.Unary
open import Data.Var hiding (_<$>_)
open import Data.Environment
open import Data.Var.Varlike
open import Data.Relation
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Zip
open import Generic.Fusion
open import Generic.Identity

open import Size
open import Function
open import Data.Sum
open import Data.Product
open import Data.List.Base hiding (lookup)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

module _ {I} (d : Desc I) {𝓥 𝓒} (S : Semantics d 𝓥 𝓒)
         (alg-fusion :
            ∀ {i σ Γ Δ Θ} (b : ⟦ d ⟧ (Scope (Tm d i)) σ Γ) {ρ₁ ρ₃} {ρ₂ : (Δ ─Env) 𝓥 Θ} →
            All Eqᴿ _ (select ρ₁ ρ₂) ρ₃ →
            let f = λ Δ σ → Semantics.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ ∘ Semantics.body Renaming ρ₁ Δ σ
                g = Semantics.body S ρ₃
            in Zip d (Kripkeᴿ Eqᴿ Eqᴿ) (fmap d f b) (fmap d g b) →
            Semantics.alg S (fmap d f b) ≡ Semantics.alg S (fmap d g b))
        where

  ren-sem : Fus (λ σ → All Eqᴿ _ ∘ (select σ)) Eqᴿ Eqᴿ d Renaming S S
  Fus.quote₁ ren-sem = λ _ t → t
  Fus.vl^𝓥₁ ren-sem = vl^Var
  Fus.thᴿ   ren-sem = λ σ ρᴿ → packᴿ (λ v → cong (λ ρ → Semantics.th^𝓥 S ρ σ) (lookupᴿ ρᴿ v))
  lookupᴿ (Fus.>>ᴿ ren-sem {Γ} {Δ} {Θ} {Ξ} {σ} {ρ₁} {ρ₂} {vs} {ws} ρᴿ vsᴿ) v with split Ξ v
  ... | inj₁ vˡ = begin
    lookup (vs >> ρ₁) (injectˡ Δ (lookup (base vl^Var) vˡ))
      ≡⟨ injectˡ->> vs ρ₁ (lookup (base vl^Var) vˡ) ⟩
    lookup vs (lookup (base vl^Var) vˡ)
      ≡⟨ cong (lookup vs) (lookup-base^Var vˡ) ⟩
    lookup vs vˡ
      ≡⟨ lookupᴿ vsᴿ vˡ ⟩
    lookup ws vˡ
      ∎
  ... | inj₂ vʳ = begin
    lookup (vs >> ρ₁) (injectʳ Ξ (lookup (base vl^Var) (lookup σ vʳ)))
      ≡⟨ injectʳ->> vs ρ₁ (lookup (base vl^Var) (lookup σ vʳ)) ⟩
    lookup ρ₁ (lookup (base vl^Var) (lookup σ vʳ))
      ≡⟨ cong (lookup ρ₁) (lookup-base^Var (lookup σ vʳ)) ⟩
    lookup ρ₁ (lookup σ vʳ)
      ≡⟨ lookupᴿ ρᴿ vʳ ⟩
    lookup ρ₂ vʳ
      ∎
  Fus.varᴿ  ren-sem = λ ρᴿ v → cong (Semantics.var S) (lookupᴿ ρᴿ v)
  Fus.algᴿ  ren-sem {Γ} {Δ} {σ} {si} {ρ₁ = ρ₁} {ρ₂} {ρ₃} b ρᴿ zp = begin
    let
      v₁  = fmap d (Semantics.body Renaming ρ₁) b
      v₃  = fmap d (Semantics.body S ρ₃) b

      aux : fmap d (λ Δ σ → Semantics.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ) v₁
          ≡ fmap d (λ Δ σ → Semantics.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ ∘ Semantics.body Renaming ρ₁ Δ σ) b
      aux = begin
        fmap d (λ Δ σ → Semantics.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ) v₁
          ≡⟨ fmap² d (Semantics.body Renaming ρ₁) (λ Δ σ → Semantics.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ) b ⟩
        fmap d (λ Δ σ → Semantics.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ ∘ Semantics.body Renaming ρ₁ Δ σ) b
          ∎
    in
    Semantics.alg S (fmap d (Semantics.body S ρ₂) (fmap d (reify vl^Var) v₁))
      ≡⟨ cong (Semantics.alg S) (fmap² d (reify vl^Var) (Semantics.body S ρ₂) (fmap d (Semantics.body Renaming ρ₁) b)) ⟩
    Semantics.alg S (fmap d (λ Δ σ → Semantics.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ) (fmap d (Semantics.body Renaming ρ₁) b))
      ≡⟨ cong (Semantics.alg S) aux ⟩
    Semantics.alg S (fmap d (λ Δ σ → Semantics.body S ρ₂ Δ σ ∘ reify vl^Var Δ σ ∘ Semantics.body Renaming ρ₁ Δ σ) b)
      ≡⟨ alg-fusion b ρᴿ (subst (λ t → Zip d _ t v₃) aux zp) ⟩
    Semantics.alg S v₃
      ∎
\end{code}
