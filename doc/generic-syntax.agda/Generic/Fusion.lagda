\begin{code}
module Generic.Fusion where

open import Size
open import Data.List hiding ([_] ; zip ; lookup)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Relation.Unary
open import Data.Relation
open import Data.Var hiding (_<$>_)
open import Data.Var.Varlike
open import Data.Environment

open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Zip

module _  {I : Set} {𝓥₁ 𝓥₂ 𝓥₃ 𝓒₁ 𝓒₂ 𝓒₃ : I ─Scoped}
          (𝓡^E : {Γ Δ Θ : List I} → (Γ ─Env) 𝓥₁ Δ → (Δ ─Env) 𝓥₂ Θ → (Γ ─Env) 𝓥₃ Θ → Set)
          (𝓡^𝓥  : Rel 𝓥₂ 𝓥₃)
          (𝓡^𝓒   : Rel 𝓒₂ 𝓒₃)
          where

 record Fus (d : Desc I) (𝓢₁ : Semantics d 𝓥₁ 𝓒₁) (𝓢₂ : Semantics d 𝓥₂ 𝓒₂) (𝓢₃ : Semantics d 𝓥₃ 𝓒₃) : Set where
   module 𝓢₁ = Semantics 𝓢₁
   module 𝓢₂ = Semantics 𝓢₂
   module 𝓢₃ = Semantics 𝓢₃
   field

     quote₁  :  (i : I) → ∀[ 𝓒₁ i ⇒ Tm d ∞ i ]

     vl^𝓥₁   :  VarLike 𝓥₁

     thᴿ    :  {Γ Δ Θ Ξ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} → (σ : Thinning Θ Ξ) → 𝓡^E ρ₁ ρ₂ ρ₃ →
                𝓡^E ρ₁ (th^Env 𝓢₂.th^𝓥 ρ₂ σ) (th^Env 𝓢₃.th^𝓥 ρ₃ σ)

     >>ᴿ    :  {Γ Δ Θ Ξ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} {ρ₄ : (Ξ ─Env) 𝓥₂ Θ} {ρ₅ : (Ξ ─Env) 𝓥₃ Θ} → 𝓡^E ρ₁ ρ₂ ρ₃ → All 𝓡^𝓥 Ξ ρ₄ ρ₅ →
                𝓡^E (freshˡ vl^𝓥₁ Δ >> th^Env 𝓢₁.th^𝓥 ρ₁ (freshʳ vl^Var Ξ)) (ρ₄ >> ρ₂) (ρ₅ >> ρ₃)

     varᴿ   :  {Γ Δ Θ : List I} {i : I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} → 𝓡^E ρ₁ ρ₂ ρ₃ → (v : Var i Γ) →
                rel 𝓡^𝓒  i (𝓢₂.semantics ρ₂ (quote₁ i (𝓢₁.var (lookup ρ₁ v))))
                             (𝓢₃.var (lookup ρ₃ v))

     algᴿ   :  {Γ Δ Θ : List I} {s : Size} {i : I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} → (b : ⟦ d ⟧ (Scope (Tm d s)) i Γ) → 𝓡^E ρ₁ ρ₂ ρ₃ →
                let  v₁ = fmap d (𝓢₁.body ρ₁) b
                     v₃ = fmap d (𝓢₃.body ρ₃) b
                in Zip d (Kripkeᴿ 𝓡^𝓥 𝓡^𝓒)
                    (fmap d (λ Δ i → 𝓢₂.body ρ₂ Δ i ∘ quote₁ i ∘ reify vl^𝓥₁ Δ i) v₁)
                    v₃ →
                rel 𝓡^𝓒 i (𝓢₂.semantics ρ₂ (quote₁ i (𝓢₁.alg v₁))) (𝓢₃.alg v₃)



   fus  :  {s : Size} {i : I} {Γ Δ Θ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Δ} {ρ₂ : (Δ ─Env) 𝓥₂ Θ} {ρ₃ : (Γ ─Env) 𝓥₃ Θ} → 𝓡^E ρ₁ ρ₂ ρ₃ → (t : Tm d s i Γ) → rel 𝓡^𝓒  i (𝓢₂.semantics ρ₂ (quote₁ i (𝓢₁.semantics ρ₁ t)))
                                                                                                                                                           (𝓢₃.semantics ρ₃ t)
   body :  {s : Size} {Γ Θ Ξ : List I} {ρ₁ : (Γ ─Env) 𝓥₁ Θ} {ρ₂ : (Θ ─Env) 𝓥₂ Ξ} {ρ₃ : (Γ ─Env) 𝓥₃ Ξ} → 𝓡^E ρ₁ ρ₂ ρ₃ → (Δ : List I) (i : I) (b : Scope (Tm d s) Δ i Γ) →
           Kripkeᴿ 𝓡^𝓥 𝓡^𝓒 Δ i   (𝓢₂.body ρ₂ Δ i (quote₁ i (reify vl^𝓥₁ Δ i (𝓢₁.body ρ₁ Δ i b))))
                                  (𝓢₃.body ρ₃ Δ i b)


   fus ρᴿ (`var v) = varᴿ ρᴿ v
   fus ρᴿ (`con t) = algᴿ t ρᴿ (rew (zip d (body ρᴿ) t)) where

     eq  = fmap² d (𝓢₁.body _) (λ Δ i t → 𝓢₂.body _ Δ i (quote₁ i (reify vl^𝓥₁ Δ i t))) t
     rew = subst (λ v → Zip d (Kripkeᴿ 𝓡^𝓥 𝓡^𝓒) v _) (sym eq)

   body ρᴿ []       i b = fus ρᴿ b
   body ρᴿ (σ ∷ Δ)  i b = λ ren vsᴿ → fus (>>ᴿ (thᴿ ren ρᴿ) vsᴿ) b


module _ {I : Set} {T : I ─Scoped} where

  open ≡-Reasoning

  -- this is the shape of environment one obtains when pushing an evaluation environment
  -- on top of a thinning into the body of a binder

  thBodyEnv :
    ∀ {Γ Δ Θ Ξ : List I} {ρ₁ : Thinning Γ Δ} {ρ₂ : (Δ ─Env) T Θ}
    {ρ₃ : (Γ ─Env) T Θ} {ρ₄ ρ₅ : (Ξ ─Env) T Θ}
    (ρᴿ : All Eqᴿ Γ (select ρ₁ ρ₂) ρ₃) (vsᴿ : All Eqᴿ Ξ ρ₄ ρ₅) →
    let σ : (Ξ ++ Γ ─Env) Var (Ξ ++ Δ)
        σ = freshˡ vl^Var Δ >> th^Env th^Var ρ₁ (freshʳ vl^Var Ξ)
    in All Eqᴿ (Ξ ++ Γ) (select σ (ρ₄ >> ρ₂)) (ρ₅ >> ρ₃)
  lookupᴿ (thBodyEnv {Γ} {Δ} {Θ} {Ξ} {ρ₁} {ρ₂} {ρ₃} {ρ₄} {ρ₅} ρᴿ vsᴿ) k
    with split Ξ k
  ... | inj₁ kˡ = begin
    lookup (ρ₄ >> ρ₂) (injectˡ Δ (lookup (base vl^Var) kˡ))
      ≡⟨ injectˡ->> ρ₄ ρ₂ (lookup (base vl^Var) kˡ) ⟩
    lookup ρ₄ (lookup (base vl^Var) kˡ)
      ≡⟨ cong (lookup ρ₄) (lookup-base^Var kˡ) ⟩
    lookup ρ₄ kˡ
      ≡⟨ lookupᴿ vsᴿ kˡ ⟩
    lookup ρ₅ kˡ
      ∎
  ... | inj₂ kʳ = begin
    lookup (ρ₄ >> ρ₂) (injectʳ Ξ (lookup (base vl^Var) (lookup ρ₁ kʳ)))
      ≡⟨ injectʳ->> ρ₄ ρ₂ (lookup (base vl^Var) (lookup ρ₁ kʳ)) ⟩
    lookup ρ₂ (lookup (base vl^Var) (lookup ρ₁ kʳ))
      ≡⟨ cong (lookup ρ₂) (lookup-base^Var (lookup ρ₁ kʳ)) ⟩
    lookup ρ₂ (lookup ρ₁ kʳ)
      ≡⟨ lookupᴿ ρᴿ kʳ ⟩
    lookup ρ₃ kʳ
      ∎

module _ {I : Set} {d : Desc I}  {𝓥 𝓒 : I ─Scoped}
         (𝓢 : Semantics d 𝓥 𝓒)
         (𝓕 : Fus (λ ρ₁ ρ₂ → All Eqᴿ _ (select ρ₁ ρ₂)) Eqᴿ Eqᴿ d Renaming 𝓢 𝓢)
         (eq^quote : ∀ σ {Γ} t → Fus.quote₁ 𝓕 σ {Γ} t ≡ t) where

  open ≡-Reasoning
  module 𝓢 = Semantics 𝓢

  SemVarTmᴿ : Rel 𝓥 𝓒
  rel SemVarTmᴿ σ v c = 𝓢.var v ≡ c

  -- this is the shape of environment one obtains when pushing an evaluation environment
  -- on top of a substitution into the body of a binder

  subBodyEnv :
    ∀ {Γ Δ Θ Ξ} (ρ₁ : (Γ ─Env) (Tm d _) Δ) {ρ₂ : (Δ ─Env) 𝓥 Θ} {ρ₃}
    {ρ₄ : (Ξ ─Env) 𝓥 Θ} {ρ₅ : (Ξ ─Env) 𝓒 Θ} →
    All Eqᴿ Γ (𝓢.semantics ρ₂ <$> ρ₁) ρ₃ →
    All SemVarTmᴿ _  ρ₄ ρ₅ →
    let σ : ((Ξ ++ Γ) ─Env) (Tm d _) (Ξ ++ Δ)
        σ = freshˡ vl^Tm Δ >> th^Env th^Tm ρ₁ (freshʳ vl^Var Ξ)
    in All Eqᴿ (Ξ ++ Γ) (𝓢.semantics (ρ₄ >> ρ₂) <$> σ) (ρ₅ >> ρ₃)
  lookupᴿ (subBodyEnv {Γ} {Δ} {Θ} {Ξ} ρ₁ {ρ₂} {ρ₃} {ρ₄} {ρ₅} ρᴿ vsᴿ) k
    with split Ξ k
  ... | inj₁ kˡ = begin
    let t = ren (pack (injectˡ Δ)) (lookup (base vl^Tm) kˡ) in
    𝓢.semantics (ρ₄ >> ρ₂) t
      ≡⟨ cong (𝓢.semantics (ρ₄ >> ρ₂)) (sym (eq^quote _ t)) ⟩
    𝓢.semantics (ρ₄ >> ρ₂) (Fus.quote₁ 𝓕 _ t)
      ≡⟨ Fus.fus 𝓕 (packᴿ (injectˡ->> ρ₄ ρ₂)) (lookup (base vl^Tm) kˡ) ⟩
    𝓢.semantics ρ₄ (lookup (base vl^Tm) kˡ)
      ≡⟨ cong (𝓢.semantics ρ₄) (lookup-base^Tm kˡ) ⟩
    𝓢.var(lookup ρ₄ kˡ)
      ≡⟨ lookupᴿ vsᴿ kˡ ⟩
    lookup ρ₅ kˡ
      ∎
  ... | inj₂ kʳ = begin
    let t = ren (freshʳ vl^Var Ξ) (lookup ρ₁ kʳ) in
    𝓢.semantics (ρ₄ >> ρ₂) t
      ≡⟨ cong (𝓢.semantics (ρ₄ >> ρ₂)) (sym (eq^quote _ t)) ⟩
    𝓢.semantics (ρ₄ >> ρ₂) (Fus.quote₁ 𝓕 _ t)
      ≡⟨ Fus.fus 𝓕 eqᴿ (lookup ρ₁ kʳ) ⟩
    𝓢.semantics ρ₂ (lookup ρ₁ kʳ)
      ≡⟨ lookupᴿ ρᴿ kʳ ⟩
    lookup ρ₃ kʳ
      ∎ where

    eqᴿ : All Eqᴿ Δ (select (freshʳ vl^Var Ξ) (ρ₄ >> ρ₂)) ρ₂
    lookupᴿ eqᴿ v = begin
      lookup (select (freshʳ vl^Var Ξ) (ρ₄ >> ρ₂)) v
        ≡⟨ injectʳ->> ρ₄ ρ₂ (lookup (base vl^Var) v) ⟩
      lookup ρ₂ (lookup (base vl^Var) v)
        ≡⟨ cong (lookup ρ₂) (lookup-base^Var v) ⟩
      lookup ρ₂ v
        ∎
\end{code}
