\begin{code}
module Properties.Simulation.Instances where

open import Data.Var hiding (_<$>_)
open import Data.Environment
open import Data.List.Base using (List; []; _∷_)
open import Data.Relation
open import Syntax.Type
open import Syntax.Calculus
open import Semantics.Specification hiding (module Fundamental)
open Semantics.Specification.Fundamental renaming (lemma to eval)
open import Semantics.Syntactic.Specification
open import Semantics.Syntactic.Instances

open import Properties.Simulation.Specification
open import Relation.Binary.PropositionalEquality.Extra

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
  𝓢 = Fundamental.syntactic Syn
\end{code}
%</synsem>
%<*syn-ext>
\begin{code}
  Syn-ext : Simulation 𝓢 𝓢 Eqᴿ Eqᴿ
  Syn-ext .th^𝓥ᴿ  = λ ρ eq → cong (λ t → th^𝓣 t ρ) eq
  Syn-ext .varᴿ   = λ ρᴿ v → cong var (lookupᴿ ρᴿ v)
  Syn-ext .lamᴿ   = λ ρᴿ b kr → cong `lam (kr extend refl)
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
  syn-ext = Fundamental.lemma Syn-ext
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
RenIsSub : Simulation Renaming Substitution VarTermᴿ Eqᴿ
RenIsSub .th^𝓥ᴿ  = λ ρ → cong (λ t → th^Term t ρ)
RenIsSub .varᴿ   = λ ρᴿ v → lookupᴿ ρᴿ v
RenIsSub .lamᴿ   = λ ρᴿ b kr → cong `lam (kr extend refl)
RenIsSub .appᴿ   = λ ρᴿ f t → cong₂ `app
RenIsSub .ifteᴿ  = λ ρᴿ b l r → cong₃ `ifte
RenIsSub .oneᴿ   = λ ρᴿ → refl
RenIsSub .ttᴿ    = λ ρᴿ → refl
RenIsSub .ffᴿ    = λ ρᴿ → refl
\end{code}
%</renissub>
%<*renassub>
\begin{code}
ren-as-sub : (t : Term σ Γ) (ρ : Thinning Γ Δ) → th^Term t ρ ≡ sub (`var <$> ρ) t
ren-as-sub t ρ = Fundamental.lemma RenIsSub (packᴿ (λ v → refl)) t
\end{code}
%</renassub>

ifteRelNorm :
  let open Semantics βιξη.Normalise in
  {Γ : Context} {σ : Type} {b^A b^B : Γ βιξη.⊨ `Bool} {l^A l^B r^A r^B : Γ βιξη.⊨ σ} →
  related _≣_ b^A b^B → related _≣_ l^A l^B → related _≣_ r^A r^B →
  related _≣_ (⟦ifte⟧ b^A l^A r^A) (⟦ifte⟧ b^B l^B r^B)
ifteRelNorm {b^A = `tt}       refl l^R r^R = l^R
ifteRelNorm {b^A = `ff}       refl l^R r^R = r^R
ifteRelNorm {b^A = `neu _ ne} refl l^R r^R =
  reflect^≣ _ (cong₂ (`ifte ne) (reify^≣ _ l^R) (reify^≣ _ r^R))

SynchronisableNormalise :  Synchronisable βιξη.Normalise βιξη.Normalise _≣_ _≣_
SynchronisableNormalise =
  record  { 𝓔^R‿wk  = λ ren ρ^R → pack^R $ wk^≣ ren ∘ lookup^R ρ^R
          ; R⟦var⟧   = λ v ρ^R → lookup^R ρ^R v
          ; R⟦$⟧     = λ f → f Env.refl
          ; R⟦λ⟧     = λ r → r
          ; R⟦⟨⟩⟧    = tt
          ; R⟦tt⟧    = refl
          ; R⟦ff⟧    = refl
          ; R⟦ifte⟧  = ifteRelNorm
          }

refl^βιξη :  {Γ Δ : Context} {σ : Type} (t : Γ ⊢ σ)
             {ρ^A ρ^B : Var Γ ⇒[ βιξη._⊨_ ] Δ} (ρ^R : `∀[ _≣_ ] ρ^A ρ^B) →
             related _≣_ (βιξη.eval t ρ^A) (βιξη.eval t ρ^B)
refl^βιξη t ρ^R = lemma SynchronisableNormalise t ρ^R where
  open Properties.Synchronisable.Specification.Fundamental
