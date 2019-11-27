\begin{code}
module Semantics.CPS.CBV where

open import Syntax.Type
open import Syntax.Calculus
open import Syntax.MoggiML.Type
open import Syntax.MoggiML.Calculus

open import Data.List.Base using (List; []; _∷_; map)
open import Data.Product as Prod hiding (map)
open import Data.Var
open import Data.Environment hiding (_<$>_; uncurry)
open import Semantics.Specification
open import Function
open import Relation.Unary
open import Relation.Binary.PropositionalEquality

private

  variable

    σ τ : Type
\end{code}
%<*cbv>
\begin{code}
mutual

  #CBV : Type → CType
  #CBV σ = # (CBV σ)

  CBV : Type → CType
  CBV `Unit     = `Unit
  CBV `Bool     = `Bool
  CBV (σ `→ τ)  = CBV σ `→# CBV τ
\end{code}
%</cbv>
\begin{code}
CBV-inj : ∀ σ τ → CBV σ ≡ CBV τ → σ ≡ τ
CBV-inj `Unit `Unit _ = refl
CBV-inj `Unit `Bool ()
CBV-inj `Unit (_ `→ _) ()
CBV-inj `Bool `Unit ()
CBV-inj `Bool `Bool _ = refl
CBV-inj `Bool (_ `→ _) ()
CBV-inj (_ `→ _) `Unit ()
CBV-inj (_ `→ _) `Bool ()
CBV-inj (σ₁ `→ τ₁) (σ₂ `→ τ₂) eq =
  uncurry (cong₂ _`→_) (Prod.map (CBV-inj σ₁ σ₂) (CBV-inj τ₁ τ₂) (`→#-inj eq))
\end{code}
%<*cbvalue>
\begin{code}
V^CBV : Type ─Scoped
V^CBV σ Γ = Var (CBV σ) (map CBV Γ)

C^CBV : Type ─Scoped
C^CBV σ Γ = ML (# CBV σ) (map CBV Γ)
\end{code}
%</cbvalue>
\begin{code}

open Semantics
\end{code}
%<*thinnable>
\begin{code}
th^V : Thinnable (V^CBV σ)
th^V v ρ = CBV <$> th^Var (mkInjective (CBV-inj _ _) <$>⁻¹ v) ρ
\end{code}
%</thinnable>
%<*lam>
\begin{code}
LAM : ∀[ □ (V^CBV σ ⇒ C^CBV τ) ⇒ C^CBV (σ `→ τ) ]
LAM b = `ret (`lam (b extend z))
\end{code}
%</lam>
%<*app>
\begin{code}
APP : ∀[ C^CBV (σ `→ τ) ⇒ C^CBV σ ⇒ C^CBV τ ]
APP f t  = `bind f (`lam (`bind (th^ML t extend) (`lam (`app (`var (s z)) (`var z)))))
\end{code}
%</app>
%<*ifte>
\begin{code}
IFTE : ∀[ C^CBV `Bool ⇒ C^CBV σ ⇒ C^CBV σ ⇒ C^CBV σ ]
IFTE b l r = `bind b (`lam (`ifte (`var z) (th^ML l extend) (th^ML r extend)))
\end{code}
%</ifte>
%<*eval>
\begin{code}
CPS : Semantics V^CBV C^CBV
CPS .th^𝓥  = th^V
CPS .var   = `ret ∘ `var
CPS .lam   = LAM
CPS .app   = APP
CPS .one   = `ret `one
CPS .tt    = `ret `tt
CPS .ff    = `ret `ff
CPS .ifte  = IFTE
\end{code}
%</eval>
