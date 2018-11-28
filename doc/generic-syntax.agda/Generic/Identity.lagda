\begin{code}
module Generic.Identity where

open import Size
open import Agda.Builtin.List
open import Data.Product hiding (zip)
open import Data.Sum
open import Data.Var
open import Data.Relation
open import Data.Var.Varlike
open import Data.Environment
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Zip
open import Generic.Simulation
open import Generic.Simulation.Syntactic

open import Function
open import Relation.Binary.PropositionalEquality as PEq
open ≡-Reasoning

-- If we directly try to prove that t[id] ≡ t we run into size-related issues.
-- So we start by definining a size-heterogeneous notion of pointwise equality
-- and then prove it equivalent to propositional equality when all sizes are ∞.

module _ {I : Set} {d : Desc I} where

-- We mutually define pointwise equality on terms and pointwise equality on
-- constructor telescopes

 data _≅_ {σ : I} {Γ : List I} : {s : Size} → Tm d s σ Γ → {t : Size} → Tm d t σ Γ → Set
 ⟨_⟩_≅_ : (e : Desc I) {σ : I} {Γ : List I} {s : Size} → ⟦ e ⟧ (Scope (Tm d s)) σ Γ → {t : Size} → ⟦ e ⟧ (Scope (Tm d t)) σ Γ → Set

-- Equality of constructors is boring; except for the size mismatch on both sides
-- and the requirement that the telescopes match up in the `con case.
 data _≅_ {σ} {Γ} where
   `var : {s t : Size} {k l : Var σ Γ} → k ≡ l → `var {s = s} k ≅ `var {s = t} l
   `con : {s t : Size} {b : ⟦ d ⟧ (Scope (Tm d s)) σ Γ} {c : ⟦ d ⟧ (Scope (Tm d t)) σ Γ} →
          ⟨ d ⟩ b ≅ c → `con b ≅ `con c

-- Equality of constructor telescopes is given to use by `Zip` together with the
-- mutually defined notion of equality
 ⟨ e ⟩ b ≅ c = Zip e (λ _ _  t u → t ≅ u) b c


-- Proof that size-heterogeneous pointwise equality coincides with propositional
-- equality when sizes are ∞
 ≅⇒≡   : ∀ {σ Γ} {t u : Tm d ∞ σ Γ} → t ≅ u → t ≡ u
 ⟨_⟩≅⇒≡ : ∀ {σ Γ} e {t u : ⟦ e ⟧ (Scope (Tm d ∞)) σ Γ} → ⟨ e ⟩ t ≅ u → t ≡ u

 ≅⇒≡ (`var eq) = cong `var eq
 ≅⇒≡ (`con eq) = cong `con (⟨ d ⟩≅⇒≡ eq)

 ⟨ `σ A d   ⟩≅⇒≡ (refl , eq) = cong -,_ (⟨ d _ ⟩≅⇒≡ eq)
 ⟨ `X Δ j d ⟩≅⇒≡ (≅-pr , eq) = cong₂ _,_ (≅⇒≡ ≅-pr) (⟨ d ⟩≅⇒≡ eq)
 ⟨ `∎ i     ⟩≅⇒≡ eq          = ≡-irrelevance _ _

-- We can now prove a lemma stating that t[id] ≅ t and we will obtain t[id] ≡ t as
-- a corrolary.

module RenId {I : Set} {d : Desc I} where

 ren-id      : ∀ {s : Size} {i Γ} (t : Tm d s i Γ) {ρ : Thinning Γ Γ} → All Eqᴿ Γ ρ (base vl^Var) → ren ρ t ≅ t
 ren-body-id : ∀ Δ i {Γ s} (t : Scope (Tm d s) Δ i Γ) {ρ : Thinning Γ Γ} → All Eqᴿ Γ ρ (base vl^Var) → reify vl^Var Δ i (Semantics.body Renaming ρ Δ i t) ≅ t

 ren-id (`var k) ρᴿ = `var (trans (lookupᴿ ρᴿ k) (lookup-base^Var k))
 ren-id (`con t) ρᴿ = `con (subst₂ (⟨ d ⟩_≅_) (sym $ fmap² d (Semantics.body Renaming _) (reify vl^Var) _) (fmap-id d _)
                            $ zip d (λ Δ i t → ren-body-id Δ i t ρᴿ) _)

 ren-body-id []        i t     = ren-id t
 ren-body-id Δ@(_ ∷ _) i {Γ} t {ρ} ρᴿ = ren-id t eqᴿ where

  eqᴿ : All Eqᴿ _ (lift vl^Var Δ ρ) (base vl^Var)
  lookupᴿ eqᴿ k with split Δ k | inspect (split Δ) k
  ... | inj₁ k₁ | PEq.[ eq ] = begin
    injectˡ Γ (lookup (base vl^Var) k₁) ≡⟨ cong (injectˡ Γ) (lookup-base^Var k₁) ⟩
    injectˡ Γ k₁                        ≡⟨ sym (lookup-base^Var k) ⟩
    lookup (base vl^Var) k              ∎
  ... | inj₂ k₂ | PEq.[ eq ] = begin
    injectʳ Δ (lookup (base vl^Var) (lookup ρ k₂)) ≡⟨ cong (injectʳ Δ) (lookup-base^Var _) ⟩
    injectʳ Δ (lookup ρ k₂)                        ≡⟨ cong (injectʳ Δ) (lookupᴿ ρᴿ k₂) ⟩
    injectʳ Δ (lookup (base vl^Var) k₂)            ≡⟨ cong (injectʳ Δ) (lookup-base^Var k₂) ⟩
    k                                              ≡⟨ sym (lookup-base^Var k) ⟩
    lookup (base vl^Var) k                         ∎

module _ {I : Set} {d : Desc I} where

  ren-id : ∀ {σ Γ} (t : Tm d ∞ σ Γ) → ren (base vl^Var) t ≡ t
  ren-id t = ≅⇒≡ (RenId.ren-id t (packᴿ λ _ → refl))

  ren-id′ : ∀ {σ Γ} (t : Tm d ∞ σ Γ) → ren (pack id) t ≡ t
  ren-id′ t = ≅⇒≡ (RenId.ren-id t (packᴿ λ v → sym (lookup-base^Var v)))

  sub-id : ∀ {σ Γ} (t : Tm d ∞ σ Γ) → sub (base vl^Tm) t ≡ t
  sub-id t = begin
    sub (base vl^Tm) t  ≡⟨ sym $ Simulation.sim RenSub base^VarTmᴿ t ⟩
    ren (base vl^Var) t ≡⟨ ren-id t ⟩
    t                   ∎

  sub-id′ : ∀ {σ Γ} (t : Tm d ∞ σ Γ) → sub (pack `var) t ≡ t
  sub-id′ t = begin
    sub (pack `var) t ≡⟨ sym $ Simulation.sim RenSub (packᴿ λ v → refl) t ⟩
    ren (pack id)   t ≡⟨ ren-id′ t ⟩
    t                 ∎

  lift[]^Tm : ∀ {Γ Δ} (ρ : (Γ ─Env) (Tm d ∞) Δ) → All Eqᴿ Γ ρ (lift vl^Tm [] ρ)
  lookupᴿ (lift[]^Tm ρ) k = sym (ren-id (lookup ρ k))


  th^base₁^Var : ∀ {Γ Δ} (ρ : Thinning {I} Γ Δ) → All Eqᴿ Γ (th^Env th^Var (base vl^Var) ρ) ρ
  lookupᴿ (th^base₁^Var ρ) k = cong (lookup ρ) (lookup-base^Var k)

  th^base₂^Var : ∀ {Γ Δ} (ρ : Thinning {I} Γ Δ) → All Eqᴿ Γ (th^Env th^Var ρ (base vl^Var)) ρ
  lookupᴿ (th^base₂^Var ρ) k = `var-inj (ren-id (`var (lookup ρ k)))

  th^base^Tm : ∀ {Γ Δ} (ρ : (Γ ─Env) (Tm d ∞) Δ) → All Eqᴿ Γ (th^Env th^Tm ρ (base vl^Var)) ρ
  lookupᴿ (th^base^Tm ρ) k = ren-id (lookup ρ k)

  th^base^s∙z : ∀ {σ Γ} → All Eqᴿ (σ ∷ Γ)  (th^Env th^Tm (base vl^Tm) (pack s) ∙ `var z)
                                           ((_ ─Env) (Tm d _) _ ∋ pack `var)
  lookupᴿ th^base^s∙z z     = refl
  lookupᴿ th^base^s∙z (s k) = cong (ren (pack s)) (lookup-base^Tm k)

\end{code}
