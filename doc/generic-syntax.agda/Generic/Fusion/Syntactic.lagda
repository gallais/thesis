\begin{code}
module Generic.Fusion.Syntactic where

open import Size
open import Data.List hiding (lookup)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function

open import Data.Var hiding (_<$>_)
open import Data.Var.Varlike
open import Data.Environment
open import Data.Relation
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Simulation
import Generic.Simulation.Syntactic as S
open import Generic.Zip
open import Generic.Identity
open import Generic.Fusion
import Generic.Fusion.Specialised.Propositional as FusProp

module _ {I : Set} (d : Desc I) where

 Ren² : Fus (λ ρ₁ → All Eqᴿ _ ∘ (select ρ₁)) Eqᴿ Eqᴿ d Renaming Renaming Renaming
 Ren² = FusProp.ren-sem d Renaming $ λ b ρᴿ zp →
   cong `con $ zip^reify Eqᴿ (reifyᴿ Eqᴿ Eqᴿ (vlᴿefl vl^Var)) d zp

 ren² : {Γ Δ Θ : List I} {i : I} {s : Size} → (t : Tm d s i Γ) (ρ₁ : Thinning Γ Δ) (ρ₂ : Thinning Δ Θ) →
        ren ρ₂ (ren ρ₁ t) ≡ ren (select ρ₁ ρ₂) t
 ren² t ρ₁ ρ₂ = Fus.fus Ren² (packᴿ (λ _ → refl)) t

 RenSub : Fus (λ ρ₁ → All Eqᴿ _ ∘ (select ρ₁)) Eqᴿ Eqᴿ d Renaming Substitution Substitution
 RenSub = FusProp.ren-sem d Substitution $ λ b ρᴿ zp →
   cong `con $ zip^reify Eqᴿ (reifyᴿ Eqᴿ Eqᴿ (vlᴿefl vl^Tm)) d zp

 rensub :  {Γ Δ Θ : List I} {i : I} {s : Size} → (t : Tm d s i Γ) (ρ₁ : Thinning Γ Δ) (ρ₂ : (Δ ─Env) (Tm d ∞) Θ) →
           sub ρ₂ (ren ρ₁ t) ≡ sub (select ρ₁ ρ₂) t
 rensub t ρ₁ ρ₂ = Fus.fus RenSub (packᴿ (λ _ → refl)) t

 SubRen : Fus (λ ρ₁ ρ₂ → All Eqᴿ _ (ren ρ₂ <$> ρ₁)) VarTmᴿ Eqᴿ d Substitution Renaming Substitution
 Fus.quote₁  SubRen = λ _ → id
 Fus.vl^𝓥₁  SubRen = vl^Tm
 Fus.thᴿ    SubRen {ρ₁ = ρ₁} {ρ₂} {ρ₃} = λ σ ρᴿ → packᴿ $ λ k →
   begin
     ren (select ρ₂ σ) (lookup ρ₁ k) ≡⟨ sym $ ren² (lookup ρ₁ k) ρ₂ σ ⟩
     ren σ (ren ρ₂ (lookup ρ₁ k))    ≡⟨ cong (ren σ) (lookupᴿ ρᴿ k) ⟩
     ren σ (lookup ρ₃ k)
   ∎
 Fus.>>ᴿ   SubRen {ρ₁ = ρ₁} = subBodyEnv Renaming Ren² (λ σ t → refl) ρ₁
 Fus.varᴿ   SubRen = λ ρᴿ v → lookupᴿ ρᴿ v
 Fus.algᴿ   SubRen {ρ₁ = ρ₁} {ρ₂} {ρ₃} b ρᴿ = λ zipped → cong `con $
   let v₁ = fmap d (Semantics.body Substitution ρ₁) b
       v₃ = fmap d (Semantics.body Substitution ρ₃) b in
   begin
     fmap d (reify vl^Var) (fmap d (Semantics.body Renaming ρ₂) (fmap d (reify vl^Tm) v₁))
         ≡⟨ cong (fmap d (reify vl^Var)) (fmap² d (reify vl^Tm) (Semantics.body Renaming ρ₂) v₁) ⟩
     fmap d (reify vl^Var) (fmap d (λ Φ i → (Semantics.body Renaming ρ₂ Φ i) ∘ (reify vl^Tm Φ i)) v₁)
         ≡⟨ zip^reify VarTmᴿ (reifyᴿ VarTmᴿ Eqᴿ vl^VarTm) d zipped ⟩
      fmap d (reify vl^Tm) v₃
   ∎

 subren :  {Γ Δ Θ : List I} {i : I} {s : Size} → ∀ (t : Tm d s i Γ) (ρ₁ : (Γ ─Env) (Tm d ∞) Δ) (ρ₂ : Thinning Δ Θ) →
           ren ρ₂ (sub ρ₁ t) ≡ sub (ren ρ₂ <$> ρ₁) t
 subren t ρ₁ ρ₂ = Fus.fus SubRen (packᴿ (λ k → refl)) t


 Sub² : Fus (λ ρ₁ ρ₂ → All Eqᴿ _ (sub ρ₂ <$> ρ₁)) Eqᴿ Eqᴿ d Substitution Substitution Substitution
 Fus.quote₁ Sub² = λ _ t → t
 Fus.vl^𝓥₁ Sub² = vl^Tm
 Fus.thᴿ Sub² {ρ₁ = ρ₁} {ρ₂} {ρ₃} = λ σ ρᴿ → packᴿ $ λ k →
   begin
     sub (ren σ <$> ρ₂) (lookup ρ₁ k) ≡⟨ sym $ subren (lookup ρ₁ k) ρ₂ σ ⟩
     ren σ (sub ρ₂ (lookup ρ₁ k))     ≡⟨ cong (ren σ) (lookupᴿ ρᴿ k)   ⟩
     ren σ (lookup ρ₃ k)
   ∎
 Fus.>>ᴿ Sub² {ρ₁ = ρ₁} = subBodyEnv Substitution RenSub (λ σ t → refl) ρ₁
 Fus.varᴿ Sub² = λ ρᴿ v → lookupᴿ ρᴿ v
 Fus.algᴿ Sub² {ρ₁ = ρ₁} {ρ₂} {ρ₃} b ρᴿ = λ zipped → cong `con $
   let v₁ = fmap d (Semantics.body Substitution ρ₁) b
       v₃ = fmap d (Semantics.body Substitution ρ₃) b in
   begin
     fmap d (reify vl^Tm) (fmap d (Semantics.body Substitution ρ₂) (fmap d (reify vl^Tm) v₁))
         ≡⟨ cong (fmap d (reify vl^Tm)) (fmap² d (reify vl^Tm) (Semantics.body Substitution ρ₂) v₁) ⟩
     fmap d (reify vl^Tm) (fmap d (λ Φ i → (Semantics.body Substitution ρ₂ Φ i) ∘ (reify vl^Tm Φ i)) v₁)
         ≡⟨ zip^reify Eqᴿ (reifyᴿ Eqᴿ Eqᴿ (vlᴿefl vl^Tm)) d zipped ⟩
      fmap d (reify vl^Tm) v₃
   ∎

 sub² :  {Γ Δ Θ : List I} {i : I} {s : Size} → ∀ (t : Tm d s i Γ) (ρ₁ : (Γ ─Env) (Tm d ∞) Δ) (ρ₂ : (Δ ─Env) (Tm d ∞) Θ) →
         sub ρ₂ (sub ρ₁ t) ≡ sub (sub ρ₂ <$> ρ₁) t
 sub² t ρ₁ ρ₂ = Fus.fus Sub² (packᴿ (λ k → refl)) t




 ren-sub-fusionᴿ : ∀ {Δ Γ Θ} (σ : (Δ ─Env) (Tm d ∞) Γ) (ρ : Thinning Γ Θ) →
   All Eqᴿ _ (select (lift vl^Var Δ ρ) (base vl^Tm <+> (ren ρ <$> σ)))
             (ren ρ <$> (base vl^Tm <+> σ))
 lookupᴿ (ren-sub-fusionᴿ {Δ} {Γ} {Θ} σ ρ) k with split Δ k
 ... | inj₁ k₁ = begin
   lookup (base vl^Tm <+> (ren ρ <$> σ)) (injectˡ Θ (lookup (base vl^Var) k₁))
     ≡⟨ injectˡ-<+> Θ (base vl^Tm) (ren ρ <$> σ) (lookup (base vl^Var) k₁) ⟩
   lookup {𝓥 = Tm d ∞} (ren ρ <$> σ) (lookup (base vl^Var) k₁)
     ≡⟨ cong (lookup {𝓥 = Tm d ∞} (ren ρ <$> σ)) (lookup-base^Var k₁) ⟩
   ren ρ (lookup σ k₁)
     ≡⟨ cong (ren ρ) (sym (injectˡ-<+> Γ (base vl^Tm) σ k₁)) ⟩
   ren ρ (lookup (base vl^Tm <+> σ) (injectˡ Γ k₁))
     ∎
 ... | inj₂ k₂ = begin
   lookup (base vl^Tm <+> (ren ρ <$> σ)) (injectʳ Δ (lookup (base vl^Var) (lookup ρ k₂)))
     ≡⟨ injectʳ-<+> Δ (base vl^Tm) (ren ρ <$> σ) (lookup (base vl^Var) (lookup ρ k₂)) ⟩
   lookup (base vl^Tm) (lookup (base vl^Var) (lookup ρ k₂))
     ≡⟨ lookup-base^Tm _ ⟩
   `var (lookup (base vl^Var) (lookup ρ k₂))
     ≡⟨ cong `var (lookup-base^Var (lookup ρ k₂)) ⟩
   ren ρ (`var k₂)
     ≡⟨ cong (ren ρ) (sym (lookup-base^Tm k₂)) ⟩
   ren ρ (lookup (base vl^Tm) k₂)
     ≡⟨ cong (ren ρ) (sym (injectʳ-<+> Δ (base vl^Tm) σ k₂)) ⟩
   ren ρ (lookup (base vl^Tm <+> σ) (injectʳ Δ k₂))
     ∎

-- Corollary

 renβ : ∀ {Δ Γ Θ s i} (b : Scope (Tm d s) Δ i Γ) (σ : (Δ ─Env) (Tm d ∞) Γ) (ρ : Thinning Γ Θ) →
        sub (base vl^Tm <+> (ren ρ <$> σ)) (ren (lift vl^Var Δ ρ) b)
        ≡ ren ρ (sub (base vl^Tm <+> σ) b)
 renβ {Δ} b σ ρ = begin
   sub (base vl^Tm <+> (ren ρ <$> σ)) (ren (lift vl^Var Δ ρ) b)
     ≡⟨ Fus.fus RenSub (ren-sub-fusionᴿ σ ρ) b ⟩
   sub (ren ρ <$> (base vl^Tm <+> σ)) b
     ≡⟨ sym (subren b (base vl^Tm <+> σ) ρ) ⟩
   ren ρ (sub (base vl^Tm <+> σ) b)
     ∎

 sub-sub-fusionᴿ : ∀ {Δ Γ Θ} (σ : (Δ ─Env) (Tm d ∞) Γ) (ρ : (Γ ─Env) (Tm d ∞) Θ) →
   All (Eqᴿ {I} {Tm d ∞}) _ (sub (base vl^Tm {Θ} <+> (sub ρ <$> σ)) <$> lift vl^Tm Δ {Γ} ρ)
                          (sub ρ <$> (base vl^Tm <+> σ))
 lookupᴿ (sub-sub-fusionᴿ {Δ} {Γ} {Θ} σ ρ) k with split Δ k
 ... | inj₁ k₁ = begin
   sub (base vl^Tm <+> (sub ρ <$> σ)) (ren (pack (injectˡ Θ)) (lookup (base vl^Tm) k₁))
     ≡⟨ cong (λ v → sub (base vl^Tm <+> (sub ρ <$> σ)) (ren (pack (injectˡ Θ)) v)) (lookup-base^Tm k₁) ⟩
   lookup (base vl^Tm <+> (sub ρ <$> σ)) (injectˡ Θ k₁)
     ≡⟨ injectˡ-<+> Θ (base vl^Tm) (sub ρ <$> σ) k₁ ⟩
   sub ρ (lookup σ k₁)
     ≡⟨ cong (sub ρ) (sym (injectˡ-<+> Γ (base vl^Tm) σ k₁)) ⟩
   sub ρ (lookup (base vl^Tm <+> σ) (injectˡ Γ k₁))
     ∎
 ... | inj₂ k₂ = begin
   sub (base vl^Tm <+> (sub ρ <$> σ)) (ren (th^Env th^Var (base vl^Var) (pack (injectʳ Δ))) (lookup ρ k₂))
     ≡⟨ Fus.fus RenSub (packᴿ (λ v → injectʳ-<+> Δ (base vl^Tm) (sub ρ <$> σ) (lookup (base vl^Var) v))) (lookup ρ k₂) ⟩
   sub (select (base vl^Var) (base vl^Tm)) (lookup ρ k₂)
     ≡⟨ Simulation.sim S.SubExt (packᴿ (λ v → cong (lookup (base vl^Tm)) (lookup-base^Var v))) (lookup ρ k₂) ⟩
   sub (base vl^Tm) (lookup ρ k₂)
     ≡⟨ sub-id (lookup ρ k₂) ⟩
   lookup ρ k₂
     ≡⟨ cong (sub ρ) (sym (lookup-base^Tm k₂)) ⟩
   sub ρ (lookup (base vl^Tm) k₂)
     ≡⟨ cong (sub ρ) (sym (injectʳ-<+> Δ (base vl^Tm) σ k₂)) ⟩
   sub ρ (lookup (base vl^Tm <+> σ) (injectʳ Δ k₂))
     ∎

 subβ : ∀ {Δ Γ Θ s i} (b : Scope (Tm d s) Δ i Γ) (σ : (Δ ─Env) (Tm d ∞) Γ) (ρ : (Γ ─Env) (Tm d ∞) Θ) →
        sub (base vl^Tm <+> (sub ρ <$> σ)) (sub (lift vl^Tm Δ ρ) b)
        ≡ sub ρ (sub (base vl^Tm <+> σ) b)
 subβ {Δ} b σ ρ = begin
   sub (base vl^Tm <+> (sub ρ <$> σ)) (sub (lift vl^Tm Δ ρ) b)
     ≡⟨ Fus.fus Sub² (sub-sub-fusionᴿ σ ρ) b ⟩
   sub (sub ρ <$> (base vl^Tm <+> σ)) b
     ≡⟨ sym (sub² b (base vl^Tm <+> σ) ρ) ⟩
   sub ρ (sub (base vl^Tm <+> σ) b)
     ∎
\end{code}
