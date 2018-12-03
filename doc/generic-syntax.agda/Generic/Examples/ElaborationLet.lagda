\begin{code}
module Generic.Examples.ElaborationLet where

open import Size
open import Data.Bool
open import Data.Product
open import Data.List.Base hiding (lookup; [_])
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Relation.Unary
open import Data.Var hiding (_<$>_)
open import Data.Relation
open import Data.Var.Varlike
open import Data.Environment
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Generic.Identity
open import Generic.Simulation as S
open import Generic.Simulation.Syntactic
open import Generic.Fusion as F
open import Generic.Fusion.Syntactic as FS
open import Generic.Zip

open Semantics

module _ {I : Set} where

\end{code}
%<*letcode>
\begin{code}
 Let : Desc I
 Let =  `σ (I × I) $ uncurry $ λ σ τ → `X [] σ (`X (σ ∷ []) τ (`∎ τ))
\end{code}
%</letcode>
\begin{code}

module _ {I : Set} {d : Desc I} where
 private variable σ : I
\end{code}
%<*letelab>
\begin{code}
 UnLet : Semantics (d `+ Let) (Tm d ∞) (Tm d ∞)
 UnLet .th^𝓥  = th^Tm
 UnLet .var    = id
 UnLet .alg    = case (Substitution .alg) λ where
   (_ , e , t , refl) → extract t (ε ∙ e)
\end{code}
%</letelab>
\begin{code}
 unLet : ∀{Γ Δ σ s} → (Γ ─Env) (Tm d ∞) Δ → Tm (d `+ Let) s σ Γ → Tm d ∞ σ Δ
 unLet ρ t = semantics UnLet ρ t
\end{code}
%<*unlet>
\begin{code}
 unlet : ∀[ Tm (d `+ Let) ∞ σ ⇒ Tm d ∞ σ ]
 unlet = Semantics.semantics UnLet (pack `var)
\end{code}
%</unlet>
\begin{code}

 open ≡-Reasoning

 proj₂-eq : ∀ {a b} {A : Set a} {B : A → Set b} {x : A} {b₁ b₂ : B x} →
            (Σ A B ∋ x , b₁) ≡ (x , b₂) → b₁ ≡ b₂
 proj₂-eq refl = refl

 RenUnLet : Fus (λ ρ₁ ρ₂ → All Eqᴿ _ (select ρ₁ ρ₂)) Eqᴿ Eqᴿ
            (d `+ Let) Renaming UnLet UnLet
 Fus.quote₁ RenUnLet = λ σ t → t
 Fus.vl^𝓥₁ RenUnLet = vl^Var
 Fus.thᴿ   RenUnLet = λ σ ρᴿ → packᴿ (cong (ren σ) ∘ lookupᴿ ρᴿ)
 Fus.>>ᴿ   RenUnLet = thBodyEnv
 Fus.varᴿ  RenUnLet = λ ρᴿ → lookupᴿ ρᴿ
 Fus.algᴿ RenUnLet (false , (_ , e , t , refl)) ρᴿ (refl , refl , eq^e , eq^t , _)
   = eq^t (pack id) (εᴿ ∙ᴿ eq^e)
 Fus.algᴿ RenUnLet {ρ₁ = ρ₁} {ρ₂} {ρ₃} (true , t) ρᴿ eq^t
   = cong `con $ begin
     let t′ = fmap d (Semantics.body Renaming ρ₁) t in
     fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₂) (fmap d (reify vl^Var) t′))
       ≡⟨ cong (fmap d (reify vl^Tm)) (fmap² d (reify vl^Var) (Semantics.body UnLet ρ₂) t′) ⟩
     fmap d (reify vl^Tm) (fmap d (λ Δ i → (Semantics.body UnLet ρ₂ Δ i) ∘ reify vl^Var Δ i) t′)
       ≡⟨ proj₂-eq $ zip^reify Eqᴿ (reifyᴿ Eqᴿ Eqᴿ (vl^Refl vl^Tm)) (d `+ Let) eq^t ⟩
     fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₃) t)
       ∎

 unLetRen : ∀ {Γ Δ Θ σ s} (t : Tm (d `+ Let) s σ Γ) {ρ₁ ρ₃} {ρ₂ : Thinning Δ Θ} →
            All Eqᴿ _ (ren ρ₂ <$> ρ₁) ρ₃ → ren ρ₂ (unLet ρ₁ t) ≡ unLet ρ₃ t
 unLetRen-body :
   ∀ Ξ σ {Γ Δ Θ s} (t : Scope (Tm (d `+ Let) s) Ξ σ Γ) {ρ₁ ρ₃} {ρ₂ : Thinning Δ Θ} →
   All Eqᴿ _ (ren ρ₂ <$> ρ₁) ρ₃ →
   reify vl^Var Ξ σ (Semantics.body Renaming ρ₂ Ξ σ (reify vl^Tm Ξ σ (Semantics.body UnLet ρ₁ Ξ σ t)))
   ≡ reify vl^Tm Ξ σ (Semantics.body UnLet ρ₃ Ξ σ t)

 unLetRen (`var v) ρᴿ = lookupᴿ ρᴿ v
 unLetRen (`con (false , (σ , τ) , e , t , refl)) {ρ₁} {ρ₃} {ρ₂} ρᴿ = unLetRen t $ packᴿ $ λ where
   z     → unLetRen e ρᴿ
   (s v) → begin
     ren ρ₂ (ren (pack id) (lookup ρ₁ v))
       ≡⟨ cong (ren ρ₂) (ren-id′ (lookup ρ₁ v)) ⟩
     ren ρ₂ (lookup ρ₁ v)
       ≡⟨ lookupᴿ ρᴿ v ⟩
     lookup ρ₃ v
       ≡⟨ sym (ren-id′ (lookup ρ₃ v)) ⟩
     ren (pack id) (lookup ρ₃ v)
       ∎
 unLetRen (`con (true  , r)) {ρ₁} {ρ₃} {ρ₂} ρᴿ = cong `con $ begin
   fmap d (reify vl^Var) (fmap d (Semantics.body Renaming ρ₂) (fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₁) r)))
     ≡⟨ fmap² d (Semantics.body Renaming ρ₂) (reify vl^Var) (fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₁) r)) ⟩
   fmap d _ (fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₁) r))
     ≡⟨ fmap² d (reify vl^Tm) _ _ ⟩
   fmap d _ (fmap d (Semantics.body UnLet ρ₁) r)
     ≡⟨ fmap² d (Semantics.body UnLet ρ₁) _ _ ⟩
   fmap d _ r
     ≡⟨ fmap-ext d (λ Ξ i b → unLetRen-body Ξ i b ρᴿ) r ⟩
   fmap d (λ Φ i → reify vl^Tm Φ i ∘ Semantics.body UnLet ρ₃ Φ i) r
     ≡⟨ sym (fmap² d (Semantics.body UnLet ρ₃) (reify vl^Tm) r) ⟩
   fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₃) r)
     ∎

 unLetRen-body [] σ t ρᴿ = unLetRen t ρᴿ
 unLetRen-body Ξ@(x ∷ xs) σ {Γ} {Δ} {Θ} t {ρ₁} {ρ₃} {ρ₂} ρᴿ = unLetRen t ρ′ᴿ where

  ρ₁₁ : Thinning Ξ (Ξ ++ Θ)
  ρ₁₁ = th^Env th^Var (base vl^Var) (pack (injectˡ Θ))
  ρ₁₂ = th^Env th^Var ρ₂ (th^Env th^Var (base vl^Var) (pack (injectʳ Ξ)))

  ρ₁₃ = pack (injectˡ Θ {Ξ}) >> th^Env th^Var ρ₂ (pack (injectʳ Ξ))

  eq₁₁ᴿ : All Eqᴿ _ ρ₁₁ (pack (injectˡ Θ))
  lookupᴿ eq₁₁ᴿ k = cong (injectˡ Θ) (lookup-base^Var k)

  eq₁₂ᴿ : All Eqᴿ _ ρ₁₂ (th^Env th^Var ρ₂ (pack (injectʳ Ξ)))
  lookupᴿ eq₁₂ᴿ k = cong (injectʳ Ξ) (lookup-base^Var (lookup ρ₂ k))

  eq₁ᴿ : All Eqᴿ _ (ρ₁₁ >> ρ₁₂) ρ₁₃
  eq₁ᴿ = eq₁₁ᴿ >>ᴿ eq₁₂ᴿ


  ρ′ᴿ : All Eqᴿ _ (ren (freshˡ vl^Var Θ >> th^Env th^Var ρ₂ (freshʳ vl^Var Ξ))
                    <$> (freshˡ vl^Tm Δ >> th^Env th^Tm  ρ₁ (freshʳ vl^Var Ξ)))
                  (freshˡ vl^Tm Θ >> th^Env th^Tm ρ₃ (freshʳ vl^Var Ξ))
  lookupᴿ ρ′ᴿ k with split Ξ k
  ... | inj₁ kˡ = begin
    ren (ρ₁₁ >> ρ₁₂) (ren (pack (injectˡ Δ)) (lookup (base vl^Tm) kˡ))
      ≡⟨ cong (ren (ρ₁₁ >> ρ₁₂) ∘ ren (pack (injectˡ Δ))) (lookup-base^Tm kˡ) ⟩
    `var (lookup (ρ₁₁ >> ρ₁₂) (injectˡ Δ kˡ))
      ≡⟨ cong `var (injectˡ->> ρ₁₁ ρ₁₂ kˡ) ⟩
    `var (lookup ρ₁₁ kˡ)
      ≡⟨ cong `var (lookupᴿ eq₁₁ᴿ kˡ) ⟩
    `var (injectˡ Θ kˡ)
      ≡⟨ cong (ren (pack (injectˡ Θ))) (sym (lookup-base^Tm kˡ)) ⟩
    ren (pack (injectˡ Θ)) (lookup (base vl^Tm) kˡ)
      ∎
  ... | inj₂ kʳ = begin
    ren (ρ₁₁ >> ρ₁₂) (ren ρ₂₁ (lookup ρ₁ kʳ))
      ≡⟨ Simulation.sim RenExt eq₁ᴿ (ren ρ₂₁ (lookup ρ₁ kʳ)) ⟩
    ren ρ₁₃ (ren ρ₂₁ (lookup ρ₁ kʳ))
      ≡⟨ cong (ren ρ₁₃) (Simulation.sim RenExt eq₂ᴿ  (lookup ρ₁ kʳ)) ⟩
    ren ρ₁₃ (ren (pack (injectʳ Ξ)) (lookup ρ₁ kʳ))
      ≡⟨ Fus.fus (Ren² d) eqᴿ (lookup ρ₁ kʳ) ⟩
    ren (select ρ₂ (pack (injectʳ Ξ))) (lookup ρ₁ kʳ)
      ≡⟨ sym (Fus.fus (Ren² d) eq₃ᴿ (lookup ρ₁ kʳ)) ⟩
    ren ρ₃₁ (ren ρ₂ (lookup ρ₁ kʳ))
      ≡⟨ cong (ren ρ₃₁) (lookupᴿ ρᴿ kʳ) ⟩
    ren ρ₃₁ (lookup ρ₃ kʳ)
      ∎ where

    ρ₂₁ = th^Env th^Var (base vl^Var) (pack (injectʳ Ξ))

    eq₂ᴿ : All Eqᴿ _ ρ₂₁ (pack (injectʳ Ξ))
    lookupᴿ eq₂ᴿ k = cong (injectʳ Ξ) (lookup-base^Var k)

    ρ₃₁ = th^Env th^Var (base vl^Var) (pack (injectʳ Ξ))

    eq₃ᴿ : All Eqᴿ _ (select ρ₂ ρ₃₁) (select ρ₂ (pack (injectʳ Ξ)))
    lookupᴿ eq₃ᴿ k = cong (injectʳ Ξ) (lookup-base^Var (lookup ρ₂ k))

    eqᴿ : All Eqᴿ _ (select (pack (injectʳ Ξ)) ρ₁₃) (select ρ₂ (pack (injectʳ Ξ)))
    lookupᴿ eqᴿ k with split Ξ (injectʳ Ξ k) | split-injectʳ Ξ k
    lookupᴿ eqᴿ k | .(inj₂ k) | refl = refl

 SubUnLet : Fus (λ ρ₁ ρ₂ → All Eqᴿ _ (unLet ρ₂ <$> ρ₁)) Eqᴿ Eqᴿ
            (d `+ Let) Substitution UnLet UnLet
 Fus.quote₁ SubUnLet = λ σ t → t
 Fus.vl^𝓥₁ SubUnLet = vl^Tm
 Fus.thᴿ   SubUnLet {ρ₁ = ρ₁} {ρ₂} {ρ₃} = λ σ ρᴿ → packᴿ λ v → begin
   Semantics.semantics UnLet (th^Env th^Tm ρ₂ σ) (lookup ρ₁ v)
     ≡⟨ sym (unLetRen (lookup ρ₁ v) (packᴿ λ v → refl)) ⟩
   ren σ (unLet ρ₂ (lookup ρ₁ v))
     ≡⟨ cong (ren σ) (lookupᴿ ρᴿ v) ⟩
   ren σ (lookup ρ₃ v)
    ∎
 Fus.>>ᴿ   SubUnLet {ρ₁ = ρ₁} = subBodyEnv UnLet RenUnLet (λ σ t → refl) ρ₁
 Fus.varᴿ  SubUnLet = λ ρᴿ → lookupᴿ ρᴿ
 Fus.algᴿ  SubUnLet (false , (_ , e , t , refl)) ρᴿ (refl , refl , eq^e , eq^t , _)
   = eq^t (pack id) (εᴿ ∙ᴿ eq^e)
 Fus.algᴿ  SubUnLet {ρ₁ = ρ₁} {ρ₂} {ρ₃} (true , t) ρᴿ eq^t
   = cong `con $ begin
     let t′ = fmap d (Semantics.body Substitution ρ₁) t in
     fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₂) (fmap d (reify vl^Tm) t′))
       ≡⟨ cong (fmap d (reify vl^Tm)) (fmap² d (reify vl^Tm) (Semantics.body UnLet ρ₂) t′) ⟩
     fmap d (reify vl^Tm) (fmap d (λ Δ i → Semantics.body UnLet ρ₂ Δ i ∘ reify vl^Tm Δ i) t′)
       ≡⟨ proj₂-eq $ zip^reify Eqᴿ (reifyᴿ Eqᴿ Eqᴿ (vl^Refl vl^Tm)) (d `+ Let) eq^t ⟩
     fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₃) t)
       ∎

 unLetSub : ∀ {Γ Δ Θ σ s} (t : Tm (d `+ Let) s σ Γ) {ρ₁ ρ₃} {ρ₂ : (Δ ─Env) (Tm d ∞) Θ} →
            All Eqᴿ _ (sub ρ₂ <$> ρ₁) ρ₃ → sub ρ₂ (unLet ρ₁ t) ≡ unLet ρ₃ t
 unLetSub-body :
   ∀ Ξ σ {Γ Δ Θ s} (t : Scope (Tm (d `+ Let) s) Ξ σ Γ) {ρ₁ ρ₃} {ρ₂ : (Δ ─Env) (Tm d ∞) Θ} →
   All Eqᴿ _ (sub ρ₂ <$> ρ₁) ρ₃ →
   reify vl^Tm Ξ σ (Semantics.body Substitution ρ₂ Ξ σ (reify vl^Tm Ξ σ (Semantics.body UnLet ρ₁ Ξ σ t)))
   ≡ reify vl^Tm Ξ σ (Semantics.body UnLet ρ₃ Ξ σ t)

 unLetSub (`var v) ρᴿ = lookupᴿ ρᴿ v
 unLetSub (`con (false , (σ , τ) , e , t , refl)) {ρ₁} {ρ₃} {ρ₂} ρᴿ = unLetSub t $ packᴿ $ λ where
   z     → unLetSub e ρᴿ
   (s v) → begin
     sub ρ₂ (ren (pack id) (lookup ρ₁ v))
       ≡⟨ cong (sub ρ₂) (ren-id′ (lookup ρ₁ v)) ⟩
     sub ρ₂ (lookup ρ₁ v)
       ≡⟨ lookupᴿ ρᴿ v ⟩
     lookup ρ₃ v
       ≡⟨ sym (ren-id′ (lookup ρ₃ v)) ⟩
     ren (pack id) (lookup ρ₃ v)
       ∎
 unLetSub (`con (true  , r)) {ρ₁} {ρ₃} {ρ₂} ρᴿ = cong `con $ begin
   fmap d (reify vl^Tm) (fmap d (Semantics.body Substitution ρ₂) (fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₁) r)))
     ≡⟨ fmap² d (Semantics.body Substitution ρ₂) (reify vl^Tm) (fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₁) r)) ⟩
   fmap d _ (fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₁) r))
     ≡⟨ fmap² d (reify vl^Tm) _ _ ⟩
   fmap d _ (fmap d (Semantics.body UnLet ρ₁) r)
     ≡⟨ fmap² d (Semantics.body UnLet ρ₁) _ _ ⟩
   fmap d _ r
     ≡⟨ fmap-ext d (λ Ξ i b → unLetSub-body Ξ i b ρᴿ) r ⟩
   fmap d (λ Φ i → reify vl^Tm Φ i ∘ Semantics.body UnLet ρ₃ Φ i) r
     ≡⟨ sym (fmap² d (Semantics.body UnLet ρ₃) (reify vl^Tm) r) ⟩
   fmap d (reify vl^Tm) (fmap d (Semantics.body UnLet ρ₃) r)
     ∎
 unLetSub-body [] σ t ρᴿ = unLetSub t ρᴿ
 unLetSub-body Ξ@(x ∷ xs) σ {Γ} {Δ} {Θ} t {ρ₁} {ρ₃} {ρ₂} ρᴿ = unLetSub t ρ′ᴿ where

  ρ₁₁ : (Ξ ─Env) (Tm d ∞) (Ξ ++ Θ)
  ρ₁₁ = th^Env th^Tm (base vl^Tm) (pack (injectˡ Θ))
  ρ₁₂ = th^Env th^Tm ρ₂ (th^Env th^Var (base vl^Var) (pack (injectʳ Ξ)))

  ρ₁₃ = pack (`var ∘ injectˡ Θ {Ξ}) >> th^Env th^Tm ρ₂ (pack (injectʳ Ξ))

  eq₁₁ᴿ : All Eqᴿ _ ρ₁₁ (pack (`var ∘ injectˡ Θ))
  lookupᴿ eq₁₁ᴿ k = cong (ren (pack (injectˡ Θ))) (lookup-base^Tm k)

  eq₁₂ᴿ : All Eqᴿ _ ρ₁₂ (th^Env th^Tm ρ₂ (pack (injectʳ Ξ)))
  lookupᴿ eq₁₂ᴿ k =
    Simulation.sim RenExt (packᴿ (cong (injectʳ Ξ) ∘ lookup-base^Var)) (lookup ρ₂ k)

  eq₁ᴿ : All Eqᴿ _ (ρ₁₁ >> ρ₁₂) ρ₁₃
  eq₁ᴿ = eq₁₁ᴿ >>ᴿ eq₁₂ᴿ

  ρ₂₁ = th^Env th^Var (base vl^Var) (pack (injectʳ Ξ))

  ρ′ᴿ : All Eqᴿ _ (sub (freshˡ vl^Tm Θ >> th^Env th^Tm ρ₂ (freshʳ vl^Var Ξ))
                    <$> (freshˡ vl^Tm Δ >> th^Env th^Tm  ρ₁ (freshʳ vl^Var Ξ)))
                  (freshˡ vl^Tm Θ >> th^Env th^Tm ρ₃ (freshʳ vl^Var Ξ))
  lookupᴿ ρ′ᴿ k with split Ξ k
  ... | inj₁ kˡ = begin
    sub (ρ₁₁ >> ρ₁₂) (ren (pack (injectˡ Δ))(lookup (base vl^Tm) kˡ))
      ≡⟨ cong (sub (ρ₁₁ >> ρ₁₂) ∘ ren (pack (injectˡ Δ))) (lookup-base^Tm kˡ) ⟩
    lookup (ρ₁₁ >> ρ₁₂) (injectˡ Δ kˡ)
      ≡⟨ injectˡ->> ρ₁₁ ρ₁₂ kˡ ⟩
    ren (pack (injectˡ Θ)) (lookup (base vl^Tm) kˡ)
      ≡⟨ cong (ren (pack (injectˡ Θ))) (lookup-base^Tm kˡ) ⟩
    `var (injectˡ Θ kˡ)
      ≡⟨ cong (ren (pack (injectˡ Θ))) (sym (lookup-base^Tm kˡ)) ⟩
    ren (pack (injectˡ Θ)) (lookup (base vl^Tm) kˡ)
      ∎
  ... | inj₂ kʳ = begin
    sub (ρ₁₁ >> ρ₁₂) (ren ρ₂₁ (lookup ρ₁ kʳ))
      ≡⟨ Simulation.sim SubExt eq₁ᴿ (ren ρ₂₁ (lookup ρ₁ kʳ)) ⟩
    sub ρ₁₃ (ren ρ₂₁ (lookup ρ₁ kʳ))
      ≡⟨ cong (sub ρ₁₃) (Simulation.sim RenExt eq₂ᴿ  (lookup ρ₁ kʳ)) ⟩
    sub ρ₁₃ (ren (pack (injectʳ Ξ)) (lookup ρ₁ kʳ))
      ≡⟨ Fus.fus (FS.RenSub d) eqᴿ (lookup ρ₁ kʳ) ⟩
    sub (th^Env th^Tm ρ₂ (pack (injectʳ Ξ))) (lookup ρ₁ kʳ)
      ≡⟨ sym (Fus.fus (SubRen d) eq₃ᴿ (lookup ρ₁ kʳ)) ⟩
    ren ρ₃₁ (sub ρ₂ (lookup ρ₁ kʳ))
      ≡⟨ cong (ren ρ₃₁) (lookupᴿ ρᴿ kʳ) ⟩
    ren ρ₃₁ (lookup ρ₃ kʳ)
      ∎ where

    eq₂ᴿ : All Eqᴿ _ ρ₂₁ (pack (injectʳ Ξ))
    lookupᴿ eq₂ᴿ k = cong (injectʳ Ξ) (lookup-base^Var k)

    ρ₃₁ = th^Env th^Var (base vl^Var) (pack (injectʳ Ξ))

    eq₃ᴿ : All Eqᴿ _ (ren ρ₃₁ <$> ρ₂) (th^Env th^Tm ρ₂ (pack (injectʳ Ξ)))
    lookupᴿ eq₃ᴿ k =
      Simulation.sim RenExt (packᴿ (cong (injectʳ Ξ) ∘ lookup-base^Var)) (lookup ρ₂ k)

    eqᴿ : All Eqᴿ _ (select (pack (injectʳ Ξ)) ρ₁₃) (th^Env th^Tm ρ₂ (pack (injectʳ Ξ)))
    lookupᴿ eqᴿ k with split Ξ (injectʳ Ξ k) | split-injectʳ Ξ k
    lookupᴿ eqᴿ k | .(inj₂ k) | refl = refl
\end{code}
