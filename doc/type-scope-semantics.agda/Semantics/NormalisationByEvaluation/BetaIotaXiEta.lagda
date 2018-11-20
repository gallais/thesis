\begin{code}

module Semantics.NormalisationByEvaluation.BetaIotaXiEta where

open import Data.Unit using (⊤)
open import Data.List.Base using (List; []; _∷_)
open import Data.Var
open import Data.Environment hiding (Kripke)
open import Syntax.Type
open import Syntax.Calculus
open import Relation.Unary
open import Function

data R^βιξη : Type → Set where
  `Bool : R^βιξη `Bool

open import Syntax.Normal R^βιξη public
open import Syntax.Normal.Thinnable
open import Semantics.Specification

private
  variable
    σ τ : Type
    Γ : List Type

\end{code}
%<*model>
\begin{code}
Model : Type ─Scoped
Model `Unit     Γ = ⊤
Model `Bool     Γ = Nf `Bool Γ
Model (σ `→ τ)  Γ = □ (Model σ ⇒ Model τ) Γ
\end{code}
%</model>
%<*thmodel>
\begin{code}
th^Model : ∀ σ → Thinnable (Model σ)
th^Model `Unit     = th^const
th^Model `Bool     = th^Nf
th^Model (σ `→ τ)  = th^□
\end{code}
%</thmodel>
\begin{code}

\end{code}
%<*reifyreflect>
\begin{code}
mutual

  var0 : ∀[ (σ ∷_) ⊢ Model σ ]
  var0 = reflect _ (`var z)

  reflect : ∀ σ → ∀[ Ne σ ⇒ Model σ ]
  reflect `Unit     t = _
  reflect `Bool     t = `neu `Bool t
  reflect (σ `→ τ)  t = λ ρ u → reflect τ (`app (th^Ne t ρ) (reify σ u))

  reify : ∀ σ → ∀[ Model σ ⇒ Nf σ ]
  reify `Unit     T = `one
  reify `Bool     T = T
  reify (σ `→ τ)  T = `lam (reify τ (T extend var0))
\end{code}
%</reifyreflect>
%<*app>
\begin{code}
APP : ∀[ Model (σ `→ τ) ⇒ Model σ ⇒ Model τ ]
APP t u = extract t u
\end{code}
%</app>
%<*ifte>
\begin{code}
IFTE : Model `Bool Γ → Model σ Γ → Model σ Γ → Model σ Γ
IFTE `tt         l r = l
IFTE `ff         l r = r
IFTE (`neu _ T)  l r = reflect _ (`ifte T (reify _ l) (reify _ r))
\end{code}
%</ifte>
\begin{code}

open Semantics
\end{code}
%<*eval>
\begin{code}
Eval : Semantics Model Model
Eval .th^𝓥  = th^Model _
Eval .var     = id
Eval .lam     = id
Eval .app     = APP
Eval .one     = _
Eval .tt      = `tt
Eval .ff      = `ff
Eval .ifte    = IFTE
\end{code}
%</eval>
%<*norm>
\begin{code}
eval : Term σ Γ → Model σ Γ
eval = Fundamental.lemma Eval (pack (reflect _ ∘ `var))

norm : Term σ Γ → Nf σ Γ
norm = reify _ ∘ eval
\end{code}
%</norm>
