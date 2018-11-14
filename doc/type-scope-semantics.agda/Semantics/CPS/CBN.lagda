\begin{code}
module Semantics.CPS.CBN where

open import Syntax.Type
open import Syntax.Calculus
open import Syntax.MoggiML.Type
open import Syntax.MoggiML.Calculus

open import Data.List.Base using (List; []; _∷_; map)
open import Data.Product as Prod hiding (map)
open import Data.Var
open import Data.Environment hiding (_<$>_)
open import Semantics.Specification
open import Function
open import Relation.Unary
open import Relation.Binary.PropositionalEquality

private

  variable

    σ τ : Type

\end{code}
%<*cbn>
\begin{code}
mutual

  #CBN : Type → CType
  #CBN σ = # (CBN σ)

  CBN : Type → CType
  CBN `Unit     = `Unit
  CBN `Bool     = `Bool
  CBN (σ `→ τ)  = #CBN σ `→# CBN τ
\end{code}
%</cbn>
\begin{code}
CBN-inj : ∀ σ τ → CBN σ ≡ CBN τ → σ ≡ τ
CBN-inj `Unit `Unit eq = refl
CBN-inj `Unit `Bool ()
CBN-inj `Unit (_ `→ _) ()
CBN-inj `Bool `Unit ()
CBN-inj `Bool `Bool eq = refl
CBN-inj `Bool (_ `→ _) ()
CBN-inj (_ `→ _) `Unit ()
CBN-inj (_ `→ _) `Bool ()
CBN-inj (σ₁ `→ τ₁) (σ₂ `→ τ₂) eq =
  uncurry (cong₂ _`→_) (Prod.map (CBN-inj σ₁ σ₂ ∘ #-inj) (CBN-inj τ₁ τ₂) (`→#-inj eq))

#CBN-inj : ∀ {σ τ} → #CBN σ ≡ #CBN τ → σ ≡ τ
#CBN-inj = CBN-inj _ _ ∘ #-inj
\end{code}
%<*cbntransformer>
\begin{code}
_^CBN : CType ─Scoped → Type ─Scoped
(T ^CBN) σ Γ = T (#CBN σ) (map #CBN Γ)
\end{code}
%</cbntransformer>
%<*thinnable>
\begin{code}
th^V : Thinnable ((Var ^CBN) σ)
th^V v ρ = #CBN <$> th^Var ((mkInjective #CBN-inj) <$>⁻¹ v) ρ
\end{code}
%</thinnable>
%<*lam>
\begin{code}
LAM : ∀[ □ ((Var ^CBN) σ ⇒ (ML ^CBN) τ) ⇒ (ML ^CBN) (σ `→ τ) ]
LAM b = `ret (`lam (b extend z))
\end{code}
%</lam>
%<*app>
\begin{code}
APP : ∀[ (ML ^CBN) (σ `→ τ) ⇒ (ML ^CBN) σ ⇒ (ML ^CBN) τ ]
APP f t = `bind f (`lam (`app (`var z) (th^ML t extend)))
\end{code}
%</app>
%<*ifte>
\begin{code}
IFTE : ∀[ (ML ^CBN) `Bool ⇒ (ML ^CBN) σ ⇒ (ML ^CBN) σ ⇒ (ML ^CBN) σ ]
IFTE b l r = `bind b (`lam (`ifte (`var z) (th^ML l extend) (th^ML r extend)))
\end{code}
%</ifte>
\begin{code}
open Semantics

\end{code}
%<*eval>
\begin{code}
CPS : Semantics (Var ^CBN) (ML ^CBN)
CPS .th^𝓥  = th^V
CPS .var   = `var
CPS .lam   = LAM
CPS .app   = APP
CPS .one   = `ret `one
CPS .tt    = `ret `tt
CPS .ff    = `ret `ff
CPS .ifte  = IFTE
\end{code}
%</eval>
