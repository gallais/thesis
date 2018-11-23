\begin{code}
module Properties.Simulation.Instances where

open import Data.Var hiding (_<$>_)
open import Data.Environment
open import Data.List.Base using (List; []; _∷_)
open import Data.Relation
open import Syntax.Type
open import Syntax.Calculus
open import Syntax.Normal.Thinnable
open import Semantics.Specification
open import Semantics.Syntactic.Specification
open import Semantics.Syntactic.Instances

open import Properties.Simulation.Specification
open import Relation.Binary.PropositionalEquality.Extra

open import Function
open Simulation

module _ 𝓣 (Syn : Syntactic 𝓣) where

  private
   variable
    Γ Δ : List Type
    σ : Type
    ρˡ ρʳ : (Γ ─Env) 𝓣 Δ

  open Syntactic Syn
\end{code}
%<*synsem>
\begin{code}[inline]
  𝓢 = syntactic Syn
\end{code}
%</synsem>
%<*syn-ext>
\begin{code}
  Syn-ext : Simulation 𝓢 𝓢 Eqᴿ Eqᴿ
  Syn-ext .th^𝓥ᴿ  = λ ρ eq → cong (λ t → th^𝓣 t ρ) eq
  Syn-ext .varᴿ   = λ ρᴿ v → cong var (lookupᴿ ρᴿ v)
  Syn-ext .lamᴿ   = λ ρᴿ b bᴿ → cong `lam (bᴿ extend refl)
  Syn-ext .appᴿ   = λ ρᴿ f t → cong₂ `app
  Syn-ext .ifteᴿ  = λ ρᴿ b l r → cong₃ `ifte
  Syn-ext .oneᴿ   = λ ρᴿ → refl
  Syn-ext .ttᴿ    = λ ρᴿ → refl
  Syn-ext .ffᴿ    = λ ρᴿ → refl
\end{code}
%</syn-ext>
%<*synext>
\begin{code}
  syn-ext : All Eqᴿ Γ ρˡ ρʳ → (t : Term σ Γ) → eval 𝓢 ρˡ t ≡ eval 𝓢 ρʳ t
  syn-ext = simulation Syn-ext
\end{code}
%</synext>

%<*varterm>
\begin{code}
VarTermᴿ : Rel Var Term
rel VarTermᴿ σ v t = `var v ≡ t
\end{code}
%</varterm>

\begin{code}
private
  variable
    σ : Type
    Γ Δ : List Type
\end{code}

%<*renissub>
\begin{code}
RenSub^Sim : Simulation Renaming Substitution VarTermᴿ Eqᴿ
RenSub^Sim .th^𝓥ᴿ  = λ ρ → cong (λ t → th^Term t ρ)
RenSub^Sim .varᴿ   = λ ρᴿ v → lookupᴿ ρᴿ v
RenSub^Sim .lamᴿ   = λ ρᴿ b bᴿ → cong `lam (bᴿ extend refl)
RenSub^Sim .appᴿ   = λ ρᴿ f t → cong₂ `app
RenSub^Sim .ifteᴿ  = λ ρᴿ b l r → cong₃ `ifte
RenSub^Sim .oneᴿ   = λ ρᴿ → refl
RenSub^Sim .ttᴿ    = λ ρᴿ → refl
RenSub^Sim .ffᴿ    = λ ρᴿ → refl
\end{code}
%</renissub>
%<*renassub>
\begin{code}
ren-as-sub : (t : Term σ Γ) (ρ : Thinning Γ Δ) → th^Term t ρ ≡ sub (`var <$> ρ) t
ren-as-sub t ρ = simulation RenSub^Sim (packᴿ (λ v → refl)) t
\end{code}
%</renassub>

\begin{code}
open import Semantics.NormalisationByEvaluation.BetaIotaXiEta


\end{code}
%<*per>
\begin{code}
PER : Rel Model Model
rel PER `Unit     t u  = t ≡ u
rel PER `Bool     t u  = t ≡ u
rel PER (σ `→ τ)  f g  = ∀ {Δ} (ρ : Thinning _ Δ) {t u} →
                         rel PER σ t u → rel PER τ (f ρ t) (g ρ u)
\end{code}
%</per>
\begin{code}

\end{code}
%<*reifyreflect>
\begin{code}
mutual

  reflectᴿ : ∀ σ {t u : Ne σ Γ} → t ≡ u → rel PER σ (reflect σ t) (reflect σ u)
  reflectᴿ `Unit     _ = refl
  reflectᴿ `Bool     t = cong (`neu `Bool) t
  reflectᴿ (σ `→ τ)  f = λ ρ t → reflectᴿ τ (cong₂ `app (cong _ f) (reifyᴿ σ t))

  reifyᴿ : ∀ σ {V W : Model σ Γ} → rel PER σ V W → reify σ V ≡ reify σ W
  reifyᴿ `Unit     EQ = refl
  reifyᴿ `Bool     EQ = EQ
  reifyᴿ (σ `→ τ)  EQ = cong `lam (reifyᴿ τ (EQ extend (reflectᴿ σ refl)))
\end{code}
%</reifyreflect>
%<*thPER>
\begin{code}
th^PER : ∀ σ {T U} → rel PER σ T U →
         ∀ (ρ : Thinning Γ Δ) → rel PER σ (th^Model σ T ρ) (th^Model σ U ρ)
th^PER `Unit     EQ ρ = refl
th^PER `Bool     EQ ρ = cong (λ t → th^Nf t ρ) EQ
th^PER (σ `→ τ)  EQ ρ = λ σ → EQ (select ρ σ)
\end{code}
%</thPER>
\begin{code}
module _ {σ Γ} {L R S T : Model σ Γ} where
\end{code}
%<*ifte>
\begin{code}
  IFTEᴿ : (B C : Model `Bool Γ) → rel PER `Bool B C →
          rel PER σ L S → rel PER σ R T → rel PER σ (IFTE B L R) (IFTE C S T)
  IFTEᴿ `tt         `tt         _     lᴿ rᴿ = lᴿ
  IFTEᴿ `ff         `ff         _     lᴿ rᴿ = rᴿ
  IFTEᴿ (`neu _ t)  (`neu _ t)  refl  lᴿ rᴿ =
    reflectᴿ σ (cong₂ (`ifte t) (reifyᴿ σ lᴿ) (reifyᴿ σ rᴿ))
\end{code}
%</ifte>
%<*nbe>
\begin{code}
Eval^Sim : Simulation Eval Eval PER PER
Eval^Sim .th^𝓥ᴿ  = λ ρ EQ → th^PER _ EQ ρ
Eval^Sim .varᴿ   = λ ρᴿ v → lookupᴿ ρᴿ v
Eval^Sim .lamᴿ   = λ ρᴿ b bᴿ → bᴿ
Eval^Sim .appᴿ   = λ ρᴿ f t fᴿ tᴿ → fᴿ (pack id) tᴿ
Eval^Sim .ifteᴿ  = λ ρᴿ b l r → IFTEᴿ _ _
Eval^Sim .oneᴿ   = λ ρᴿ → refl
Eval^Sim .ttᴿ    = λ ρᴿ → refl
Eval^Sim .ffᴿ    = λ ρᴿ → refl
\end{code}
%</nbe>

