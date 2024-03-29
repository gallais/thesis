\begin{code}
module Semantics.NormalisationByEvaluation.BetaIotaXi where

open import Data.Unit using (⊤)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Base using (List; []; _∷_)
open import Data.Var
open import Data.Environment hiding (Kripke)
open import Syntax.Type
open import Syntax.Calculus
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function

\end{code}
%<*noeta>
\begin{code}
NoEta^βιξ : Type → Set
NoEta^βιξ _ = ⊤
\end{code}
%</noeta>
\begin{code}

open import Syntax.Normal NoEta^βιξ
open import Syntax.Normal.Thinnable
open import Semantics.Specification
open import Semantics.NormalisationByEvaluation.Specification

private

  variable

    σ τ : Type
    Γ Δ : List Type

\end{code}
%<*model>
\begin{code}
mutual

  Model : Type ─Scoped
  Model σ Γ = Ne σ Γ ⊎ Value σ Γ

  Value : Type ─Scoped
  Value `Unit     = const ⊤
  Value `Bool     = const Bool
  Value (σ `→ τ)  = □ (Model σ ⇒ Model τ)
\end{code}
%</model>
%<*thmodel>
\begin{code}
th^Value : ∀ σ → Thinnable (Value σ)
th^Value `Unit     = th^const
th^Value `Bool     = th^const
th^Value (σ `→ τ)  = th^□

th^Model : ∀ σ → Thinnable (Model σ)
th^Model σ (inj₁ neu)  ρ = inj₁ (th^Ne neu ρ)
th^Model σ (inj₂ val)  ρ = inj₂ (th^Value σ val ρ)
\end{code}
%</thmodel>
\begin{code}

\end{code}
%<*reflect>
\begin{code}
reflect : ∀[ Ne σ ⇒ Model σ ]
reflect = inj₁

var0 : ∀[ (σ ∷_) ⊢ Model σ ]
var0 = reflect (`var z)
\end{code}
%</reflect>
%<*reify>
\begin{code}
mutual

  reify : ∀ σ → ∀[ Model σ ⇒ Nf σ ]
  reify σ (inj₁ neu)  = `neu _ neu
  reify σ (inj₂ val)  = reify^Value σ val

  reify^Value : ∀ σ → ∀[ Value σ ⇒ Nf σ ]
  reify^Value `Unit     _ = `one
  reify^Value `Bool     b = if b then `tt else `ff
  reify^Value (σ `→ τ)  f = `lam (reify τ (f extend var0))
\end{code}
%</reify>
\begin{code}
module _ {σ τ} where
\end{code}
%<*app>
\begin{code}
 APP : ∀[ Model (σ `→ τ) ⇒ Model σ ⇒ Model τ ]
 APP (inj₁ f) t = inj₁ (`app f (reify σ t))
 APP (inj₂ f) t = extract f t
\end{code}
%</app>
\begin{code}
module _ {σ} where
\end{code}
%<*ifte>
\begin{code}
 IFTE : ∀[ Model `Bool ⇒ Model σ ⇒ Model σ ⇒ Model σ ]
 IFTE (inj₁ b) l r = inj₁ (`ifte b (reify σ l) (reify σ r))
 IFTE (inj₂ b) l r = if b then l else r
\end{code}
%</ifte>
\begin{code}
open Semantics

\end{code}
%<*eval>
\begin{code}
Eval : Semantics Model Model
Eval .th^𝓥  = th^Model _
Eval .var   = id
Eval .lam   = inj₂
Eval .app   = APP
Eval .one   = inj₂ _
Eval .tt    = inj₂ true
Eval .ff    = inj₂ false
Eval .ifte  = IFTE
\end{code}
%</eval>
%<*norm>
\begin{code}
nbe : NBE Model Nf
nbe = record
  { Sem    = Eval
  ; embed  = reflect ∘ `var
  ; reify  = reify _
  }
\end{code}
%</norm>

\begin{code}
open NBE using (test)
\end{code}

%<*test>
\begin{code}
_ : test nbe ≡ `lam (`lam (`neu _ (`ifte (`var (s z)) `one (`neu _ (`var z)))))
_ = refl
\end{code}
%</test>
