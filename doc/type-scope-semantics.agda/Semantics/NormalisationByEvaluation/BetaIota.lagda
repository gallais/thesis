\begin{code}
module Semantics.NormalisationByEvaluation.BetaIota where

open import Data.Unit using (⊤)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product

open import Data.Var
open import Data.Environment hiding (Kripke)
open import Syntax.Type
open import Syntax.Calculus
open import Semantics.Syntactic.Instances
open import Relation.Unary
open import Function

open import Syntax.WeakHead
open import Semantics.Specification hiding (eval)

private

  variable

    σ τ : Type

\end{code}
%<*model>
\begin{code}
mutual

  Model : Type ─Scoped
  Model σ Γ = Term σ Γ × (WHNE σ Γ ⊎ Value σ Γ)

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
th^Model σ (t , inj₁ whne)  ρ = th^Term t ρ , inj₁ (th^WHNE whne ρ)
th^Model σ (t , inj₂ val)   ρ = th^Term t ρ , inj₂ (th^Value σ val ρ)
\end{code}
%</thmodel>
\begin{code}

\end{code}
%<*reifyreflect>
\begin{code}
reflect : ∀[ WHNE σ ⇒ Model σ ]
reflect = < erase^WHNE , inj₁ >

var0 : ∀[ (σ ∷_) ⊢ Model σ ]
var0 = reflect (`var z)

mutual

  reify : ∀[ Model σ ⇒ WHNF σ ]
  reify (t , inj₁ whne)  = `whne whne
  reify (t , inj₂ val)   = reify^Value _ val

  reify^Value : ∀ σ → ∀[ Value σ ⇒ WHNF σ ]
  reify^Value `Unit     v = `one
  reify^Value `Bool     v = if v then `tt else `ff
  reify^Value (σ `→ τ)  v = `lam (proj₁ (v extend var0))
\end{code}
%</reifyreflect>
%<*app>
\begin{code}
APP : ∀[ Model (σ `→ τ) ⇒ Model σ ⇒ Model τ ]
APP (f , inj₁ whne)  (t , _)  = (`app f t , inj₁ (`app whne t))
APP (_ , inj₂ f)     t        = extract f t
\end{code}
%</app>
%<*ifte>
\begin{code}
IFTE : ∀[ Model `Bool ⇒ Model σ ⇒ Model σ ⇒ Model σ ]
IFTE (b , inj₁ whne)  (l , _)  (r , _)  = (`ifte b l r , inj₁ (`ifte whne l r))
IFTE (b , inj₂ v)     l         r       = if v then l else r
\end{code}
%</ifte>
%<*lam>
\begin{code}
LAM : ∀[ □ (Model σ ⇒ Model τ) ⇒ Model (σ `→ τ) ]
LAM b = (`lam (proj₁ (b extend var0)) , inj₂ b)
\end{code}
%</lam>
\begin{code}
open Semantics

\end{code}
%<*eval>
\begin{code}
Eval : Semantics Model Model
Eval .th^𝓥  = th^Model _
Eval .var   = id
Eval .lam   = LAM
Eval .app   = APP
Eval .one   = `one , inj₂ _
Eval .tt    = `tt , inj₂ true
Eval .ff    = `ff , inj₂ false
Eval .ifte  = IFTE
\end{code}
%</eval>
%<*whnorm>
\begin{code}
eval : ∀[ Term σ ⇒ Model σ ]
eval = Fundamental.lemma Eval (pack (reflect ∘ `var))

whnorm : ∀[ Term σ ⇒ WHNF σ ]
whnorm = reify ∘ eval
\end{code}
%</whnorm>
