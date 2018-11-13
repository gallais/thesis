\begin{code}
module Syntax.MoggiML.Calculus where

open import Syntax.MoggiML.Type
open import Data.List.Base using (List; []; _∷_)
open import Data.Var
open import Data.Environment
open import Relation.Unary

private

  variable

    σ τ : CType

\end{code}
%<*calculus>
\begin{code}
data ML : CType ─Scoped where
  `var     : ∀[ Var σ ⇒ ML σ ]
  `app     : ∀[ ML (σ `→# τ) ⇒ ML σ ⇒ ML (# τ) ]
  `lam     : ∀[ (σ ∷_) ⊢ ML (# τ) ⇒ ML (σ `→# τ) ]
  `one     : ∀[ ML `Unit ]
  `tt `ff  : ∀[ ML `Bool ]
  `ifte    : ∀[ ML `Bool ⇒ ML (# σ) ⇒ ML (# σ) ⇒ ML (# σ) ]
  `ret     : ∀[ ML σ ⇒ ML (# σ) ]
  `bind    : ∀[ ML (# σ) ⇒ ML (σ `→# τ) ⇒ ML (# τ) ]
\end{code}
%</calculus>
%<*thcalculus>
\begin{code}
th^ML : Thinnable (ML σ)
th^ML (`var v)       ρ = `var (lookup ρ v)
th^ML (`app f t)     ρ = `app (th^ML f ρ) (th^ML t ρ)
th^ML (`lam b)       ρ = `lam (th^ML b (th^Env th^Var ρ extend ∙ z))
th^ML `one           ρ = `one
th^ML `tt            ρ = `tt
th^ML `ff            ρ = `ff
th^ML (`ifte t l r)  ρ = `ifte (th^ML t ρ) (th^ML l ρ) (th^ML r ρ)
th^ML (`ret t)       ρ = `ret (th^ML t ρ)
th^ML (`bind m f)    ρ = `bind (th^ML m ρ) (th^ML f ρ)
\end{code}
%</thcalculus>
