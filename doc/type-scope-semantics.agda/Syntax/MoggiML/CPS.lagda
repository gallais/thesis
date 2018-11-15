\begin{code}
module Syntax.MoggiML.CPS where

open import Syntax.Type
open import Syntax.Calculus
open import Semantics.Syntactic.Instances
open import Syntax.MoggiML.Type
open import Syntax.MoggiML.Calculus

open import Data.List.Base
open import Data.Var
open import Data.Environment hiding (_<$>_)
open import Function renaming (_$′_ to _$_; _∘′_ to _∘_) using ()

private

  variable

     r : Type
     σ τ : CType
     Γ : List CType
\end{code}
%<*cps>
\begin{code}
mutual

  #CPS[_] : Type → CType → Type
  #CPS[ r ] σ = (CPS[ r ] σ `→ r) `→ r

  CPS[_] : Type → CType → Type
  CPS[ r ] `Bool      = `Bool
  CPS[ r ] `Unit      = `Unit
  CPS[ r ] (σ `→# τ)  = CPS[ r ] σ `→ #CPS[ r ] τ
  CPS[ r ] (# σ)      = #CPS[ r ] σ
\end{code}
%</cps>
%<*elabtype>
\begin{code}
cps : ML σ Γ → Term (CPS[ r ] σ) (map CPS[ r ] Γ)
\end{code}
%</elabtype>
%<*elab>
\begin{code}
cps (`var v)       = `var (CPS[ _ ] <$> v)
cps (`app f t)     = `app (cps f) (cps t)
cps (`lam b)       = `lam (cps b)
cps `one           = `one
cps `tt            = `tt
cps `ff            = `ff
cps (`ifte b l r)  = `ifte (cps b) (cps l) (cps r)
\end{code}
%</elab>
%<*elabret>
\begin{code}
cps (`ret t)       = `lam (`app (`var z) (th^Term (cps t) extend))
\end{code}
%</elabret>
%<*elabbind>
\begin{code}
cps (`bind m f)    = `lam $ `app m' $ `lam $ `app (`app f' (`var z)) (`var (s z))
  where  m'  = th^Term (cps m) (pack s)
         f'  = th^Term (cps f) (pack (s ∘ s))
\end{code}
%</elabbind>
