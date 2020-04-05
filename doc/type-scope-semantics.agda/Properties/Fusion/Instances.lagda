\begin{code}
module Properties.Fusion.Instances where

open import Data.Var hiding (_<$>_)
open import Data.Environment
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Relation as Rel hiding (_∙ᴿ_)
open import Syntax.Type
open import Syntax.Calculus
open import Semantics.Specification as Semantics
open import Semantics.Syntactic.Instances
open import Function renaming (_$′_ to _$_) using (id)
open import Relation.Unary

open import Relation.Binary.PropositionalEquality.Extra
open import Properties.Simulation.Instances
  using (PER; refl^PER; sym^PER; trans^PER; th^PER; reflectᴿ; reifyᴿ; eval^Sim)
open import Semantics.NormalisationByEvaluation.BetaIotaXiEta
open import Properties.Fusion.Specification

eval = Semantics.semantics Eval

module RenFusion where

\end{code}
%<*crel>
\begin{code}
 𝓡 :  ∀ {Γ Δ Θ} σ (ρᴬ : Thinning Γ Δ) (ρᴮ : (Δ ─Env) Model Θ)
      (ρᴬᴮ : (Γ ─Env) Model Θ) → Term σ Γ → Set
 𝓡 σ ρᴬ ρᴮ ρᴬᴮ t = rel PER σ (eval ρᴮ (th^Term t ρᴬ)) (eval ρᴬᴮ t)
\end{code}
%</crel>
\begin{code}
 module _ {Γ Δ Θ σ τ} {ρᴬ : Thinning Γ Δ} {ρᴮ : (Δ ─Env) Model Θ} {ρᴬᴮ : (Γ ─Env) Model Θ} where

\end{code}
%<*appR>
\begin{code}
  APPᴿ :  ∀ f t → 𝓡 (σ `→ τ) ρᴬ ρᴮ ρᴬᴮ f → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ t →
          𝓡 τ ρᴬ ρᴮ ρᴬᴮ (`app f t)
  APPᴿ f t fᴿ tᴿ = fᴿ identity tᴿ
\end{code}
%</appR>
\begin{code}

 module _ {Γ Δ Θ σ} {ρᴬ : Thinning Γ Δ} {ρᴮ : (Δ ─Env) Model Θ} {ρᴬᴮ : (Γ ─Env) Model Θ} where
\end{code}
%<*ifteR>
\begin{code}
  IFTEᴿ : ∀ b l r → 𝓡 `Bool ρᴬ ρᴮ ρᴬᴮ b → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ l → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ r →
          𝓡 σ ρᴬ ρᴮ ρᴬᴮ (`ifte b l r)
  IFTEᴿ b l r bᴿ lᴿ rᴿ with eval ρᴮ (th^Term b ρᴬ) | eval ρᴬᴮ b
  ... | `tt        | `tt        = lᴿ
  ... | `ff        | `ff        = rᴿ
  ... | `neu _ b₁  | `neu _ b₂  =
    reflectᴿ σ $ cong₃ `ifte (`neu-injective bᴿ) (reifyᴿ σ lᴿ) (reifyᴿ σ rᴿ)
\end{code}
%</ifteR>
\begin{code}
  IFTEᴿ b l r () lᴿ rᴿ | `neu _ _   | `ff
  IFTEᴿ b l r () lᴿ rᴿ | `neu _ _   | `tt
  IFTEᴿ b l r () lᴿ rᴿ | `ff        | `neu _ _
  IFTEᴿ b l r () lᴿ rᴿ | `ff        | `tt
  IFTEᴿ b l r () lᴿ rᴿ | `tt        | `neu _ _
  IFTEᴿ b l r () lᴿ rᴿ | `tt        | `ff

 private
   variable
     Γ Δ Θ : List Type
     σ τ : Type

 open Fusion

\end{code}
%<*reneval>
\begin{code}
 RenEval : Fusion  Renaming Eval Eval
                   (λ ρᴬ ρᴮ → All PER _ (select ρᴬ ρᴮ)) PER PER
 RenEval .reifyᴬ   = id
 RenEval .var0ᴬ    = z
 RenEval ._∙ᴿ_     = λ ρᴿ vᴿ → vᴿ ∷ᴿ lookupᴿ ρᴿ
 RenEval .th^𝓔ᴿ    = λ ρᴿ ρ → (λ v → th^PER _ v ρ) <$>ᴿ ρᴿ
 RenEval .varᴿ     = λ ρᴿ → lookupᴿ ρᴿ
 RenEval .oneᴿ     = λ ρᴿ → refl
 RenEval .ttᴿ      = λ ρᴿ → refl
 RenEval .ffᴿ      = λ ρᴿ → refl
 RenEval .appᴿ     = λ ρᴿ → APPᴿ
 RenEval .ifteᴿ    = λ ρᴿ → IFTEᴿ
 RenEval .lamᴿ     = λ ρᴿ b bᴿ → bᴿ
\end{code}
%</reneval>
%<*renevalfun>
\begin{code}
 reneval :  (th : Thinning Γ Δ) (ρ : (Δ ─Env) Model Θ) → All PER Δ ρ ρ →
            ∀ t → rel PER σ (eval ρ (th^Term t th)) (eval (select th ρ) t)
 reneval th ρ ρᴿ t = fusion RenEval (selectᴿ th ρᴿ) t
\end{code}
%</renevalfun>
\begin{code}
open RenFusion using (reneval)

module SubFusion where
\end{code}
%<*crel>
\begin{code}
 𝓡 :  ∀ {Γ Δ Θ} σ (ρᴬ : (Γ ─Env) Term Δ) (ρᴮ : (Δ ─Env) Model Θ)
      (ρᴬᴮ : (Γ ─Env) Model Θ) → Term σ Γ → Set
 𝓡 σ ρᴬ ρᴮ ρᴬᴮ t = rel PER σ (eval ρᴮ (sub ρᴬ t)) (eval ρᴬᴮ t)
\end{code}
%</crel>
\begin{code}
 module _ {Γ Δ Θ σ τ} {ρᴬ : (Γ ─Env) Term Δ} {ρᴮ : (Δ ─Env) Model Θ} {ρᴬᴮ : (Γ ─Env) Model Θ} where

\end{code}
%<*appR>
\begin{code}
  APPᴿ : ∀ f t → 𝓡 (σ `→ τ) ρᴬ ρᴮ ρᴬᴮ f → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ t → 𝓡 τ ρᴬ ρᴮ ρᴬᴮ (`app f t)
  APPᴿ f t fᴿ tᴿ = fᴿ identity tᴿ
\end{code}
%</appR>
\begin{code}

 module _ {Γ Δ Θ σ} {ρᴬ : (Γ ─Env) Term Δ} {ρᴮ : (Δ ─Env) Model Θ} {ρᴬᴮ : (Γ ─Env) Model Θ} where
\end{code}
%<*ifteR>
\begin{code}
  IFTEᴿ : ∀ b l r → 𝓡 `Bool ρᴬ ρᴮ ρᴬᴮ b → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ l → 𝓡 σ ρᴬ ρᴮ ρᴬᴮ r →
          𝓡 σ ρᴬ ρᴮ ρᴬᴮ (`ifte b l r)
  IFTEᴿ b l r bᴿ lᴿ rᴿ with eval ρᴮ (sub ρᴬ b) | eval ρᴬᴮ b
  ... | `tt        | `tt        = lᴿ
  ... | `ff        | `ff        = rᴿ
  ... | `neu _ b₁  | `neu _ b₂  =
    reflectᴿ σ $ cong₃ `ifte (`neu-injective bᴿ) (reifyᴿ σ lᴿ) (reifyᴿ σ rᴿ)
\end{code}
%</ifteR>
\begin{code}
  IFTEᴿ b l r () lᴿ rᴿ | `neu _ _   | `ff
  IFTEᴿ b l r () lᴿ rᴿ | `neu _ _   | `tt
  IFTEᴿ b l r () lᴿ rᴿ | `ff        | `neu _ _
  IFTEᴿ b l r () lᴿ rᴿ | `ff        | `tt
  IFTEᴿ b l r () lᴿ rᴿ | `tt        | `neu _ _
  IFTEᴿ b l r () lᴿ rᴿ | `tt        | `ff


 private
   variable
     Γ Δ Θ : List Type
     σ τ : Type

 open Fusion

 module _ {Γ Δ Θ : List Type} where
\end{code}
%<*subr>
\begin{code}
  Subᴿ : (Γ ─Env) Term Δ → (Δ ─Env) Model Θ → (Γ ─Env) Model Θ → Set
  Subᴿ ρᴬ ρᴮ ρᴬᴮ  = All PER Δ ρᴮ ρᴮ × All PER Γ ρᴬᴮ ρᴬᴮ ×
    (∀ {Ω} (ρ : Thinning Θ Ω) →
    All PER Γ (eval (th^Env (th^Model _) ρᴮ ρ) <$> ρᴬ)
              (th^Env (th^Model _) ρᴬᴮ ρ))
\end{code}
%</subr>
\begin{code}

 th^Model-id : ∀ σ → {v : Model σ Γ} → rel PER σ v v → rel PER σ (th^Model σ v (pack id)) v
 th^Model-id `Unit     vᴿ = refl
 th^Model-id `Bool     vᴿ = th^Nf-id _ reflᴿ
 th^Model-id (σ `→ τ)  vᴿ = vᴿ

 th^Model² : ∀ σ → {v : Model σ Γ} → rel PER σ v v →
             ∀ (ρ₁ : Thinning Γ Δ) (ρ₂ : Thinning Δ Θ) →
             rel PER σ (th^Model σ (th^Model σ v ρ₁) ρ₂) (th^Model σ v (select ρ₁ ρ₂))
 th^Model² `Unit     vᴿ ρ₁ ρ₂ = refl
 th^Model² `Bool     vᴿ ρ₁ ρ₂ = th^Nf-compose _ reflᴿ
 th^Model² (σ `→ τ)  vᴿ ρ₁ ρ₂ = λ ρ → vᴿ (select ρ₁ (select ρ₂ ρ))

 module _ {Γ Δ Θ σ} (ρᴬ : (Γ ─Env) Term Δ) {ρᴮ : (Δ ─Env) Model Θ} {ρᴬᴮ : (Γ ─Env) Model Θ}
          {vᴮ vᴬᴮ : Model σ Θ} where
   ∙ᴿ₃ : Subᴿ ρᴬ ρᴮ ρᴬᴮ → rel PER σ vᴮ vᴬᴮ →
         Subᴿ (th^Env th^Term ρᴬ extend ∙ `var z) (ρᴮ ∙ vᴮ) (ρᴬᴮ ∙ vᴬᴮ)
   ∙ᴿ₃ (ρᴿᴮ , ρᴿᴬᴮ , ρᴿ) vᴿ =
       ρᴿᴮ Rel.∙ᴿ refl^PER _ vᴿ
     , ρᴿᴬᴮ Rel.∙ᴿ refl^PER _ (sym^PER _ vᴿ)
     , λ ρ → packᴿ λ where
         z     → th^PER _ vᴿ ρ
         (s v) → let t    = lookup ρᴬ v
                     ρᴮ′  = th^Env (th^Model _) (ρᴮ ∙ vᴮ) ρ
                     ρᴿᴮ′ = (λ eq → th^PER _ eq ρ) <$>ᴿ (ρᴿᴮ Rel.∙ᴿ refl^PER _ vᴿ)
                 in
             trans^PER _ (reneval extend ρᴮ′ ρᴿᴮ′ t)
           $ trans^PER _ (eval^Sim (packᴿ λ k → th^PER _ (lookupᴿ ρᴿᴮ k) ρ) t)
           $ lookupᴿ (ρᴿ ρ) v
\end{code}
%<*subeval>
\begin{code}
 SubEval : Fusion Substitution Eval Eval Subᴿ PER PER
\end{code}
%</subeval>
\begin{code}
 SubEval .reifyᴬ   = id
 SubEval .var0ᴬ    = `var z
 SubEval ._∙ᴿ_ {ρᴬ = ρᴬ} ρᴿ vᴿ = ∙ᴿ₃ ρᴬ ρᴿ vᴿ
 SubEval .th^𝓔ᴿ {ρᴬ = ρᴬ} (ρᴿᴮ , ρᴿᴬᴮ , ρᴿ) ρ =
     ((λ eq → th^PER _ eq ρ) <$>ᴿ ρᴿᴮ)
   , ((λ eq → th^PER _ eq ρ) <$>ᴿ ρᴿᴬᴮ)
   , λ ρ′ → packᴿ λ k →
     trans^PER _ (eval^Sim (packᴿ λ k′ → th^Model² _ (lookupᴿ ρᴿᴮ k′) ρ ρ′) (lookup ρᴬ k))
   $ trans^PER _ (lookupᴿ (ρᴿ (select ρ ρ′)) k)
   $ sym^PER _ (th^Model² _ (lookupᴿ ρᴿᴬᴮ k) ρ ρ′)
 SubEval .varᴿ {ρᴬ = ρᴬ} (ρᴿᴮ , ρᴿᴬᴮ , ρᴿ) v = let t = lookup ρᴬ v in
     trans^PER _ (eval^Sim (packᴿ λ k → sym^PER _ (th^Model-id _ (lookupᴿ ρᴿᴮ k))) t)
   $ trans^PER _ (lookupᴿ (ρᴿ (pack id)) v)
   $ th^Model-id _ (lookupᴿ ρᴿᴬᴮ v)
 SubEval .oneᴿ     = λ ρᴿ → refl
 SubEval .ttᴿ      = λ ρᴿ → refl
 SubEval .ffᴿ      = λ ρᴿ → refl
 SubEval .appᴿ     = λ ρᴿ → APPᴿ
 SubEval .ifteᴿ    = λ ρᴿ → IFTEᴿ
 SubEval .lamᴿ     = λ ρᴿ b bᴿ → bᴿ
\end{code}
