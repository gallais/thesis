\begin{code}

module Semantics.NormalisationByEvaluation.BetaIotaXiEta where

open import Data.Unit using (⊤)
open import Data.List.Base using (List; []; _∷_)
open import Data.Var
open import Data.Environment as Env hiding (Kripke; Thinning)
open import Syntax.Type
open import Syntax.Calculus hiding (module DISPLAYONLY)
open import Relation.Unary
open import Function

\end{code}
%<*noeta>
\begin{code}
data NoEta^βιξη : Type → Set where
  `Bool : NoEta^βιξη `Bool
\end{code}
%</noeta>
\begin{code}


open import Syntax.Normal NoEta^βιξη public
open import Syntax.Normal.Thinnable
open import Semantics.Specification
open import Semantics.NormalisationByEvaluation.Specification

open import Agda.Builtin.Equality

private
  variable
    σ τ : Type
    Γ : List Type

module DISPLAYONLY where
\end{code}
%<*model>
\begin{code}
 Model : Type ─Scoped
 Model `Unit     = const ⊤
 Model `Bool     = Nf `Bool
 Model (σ `→ τ)  = □ (Model σ ⇒ Model τ)
\end{code}
%</model>
\begin{code}
Model : Type ─Scoped
Model `Unit     Γ = ⊤
Model `Bool     Γ = Nf `Bool Γ
Model (σ `→ τ)  Γ = □ (Model σ ⇒ Model τ) Γ
\end{code}
%<*thmodel>
\begin{code}
th^Model : ∀ σ → Thinnable (Model σ)
th^Model `Unit     = th^const
th^Model `Bool     = th^Nf
th^Model (σ `→ τ)  = th^□
\end{code}
%</thmodel>
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
\begin{code}
module _ {σ} where
\end{code}
%<*ifte>
\begin{code}
 IFTE : Model `Bool Γ → Model σ Γ → Model σ Γ → Model σ Γ
 IFTE `tt         l r = l
 IFTE `ff         l r = r
 IFTE (`neu _ T)  l r = reflect σ (`ifte T (reify σ l) (reify σ r))
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
Eval .lam   = id
Eval .app   = APP
Eval .one   = _
Eval .tt    = `tt
Eval .ff    = `ff
Eval .ifte  = IFTE
\end{code}
%</eval>
%<*norm>
\begin{code}
nbe : NBE Model Nf
nbe = record
  { Sem    = Eval
  ; embed  = reflect _ ∘ `var
  ; reify  = reify _
  }
\end{code}
%</norm>

\begin{code}
open NBE using (test)
\end{code}

%<*test>
\begin{code}
_ : test nbe ≡ `lam (`lam `one)
_ = refl
\end{code}
%</test>
%<*exotic>
\begin{code}
exotic : Model (`Bool `→ `Bool) []
exotic {_ ∷ `Bool ∷ Δ}  ρ b = `neu `Bool (`var (s z))
exotic {_}              ρ b = b
\end{code}
%</exotic>

\begin{code}
open import Relation.Binary.PropositionalEquality
private
  Thinning = Env.Thinning {I = Type}

2⇒2 : Type
2⇒2 = `Bool `→ `Bool
\end{code}
%<*exotictest>
\begin{code}
_ : th^Nf (reify 2⇒2 exotic) (bind `Bool) ≡ `lam (`neu `Bool (`var z))
_ = refl

_ : reify 2⇒2 (th^Model 2⇒2 exotic (bind `Bool)) ≡ `lam (`neu `Bool (`var (s z)))
_ = refl
\end{code}
%</exotictest>
