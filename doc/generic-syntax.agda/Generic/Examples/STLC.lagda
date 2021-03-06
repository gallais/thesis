\begin{code}
module Generic.Examples.STLC where

open import Size
open import Data.Bool
open import Data.Product
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Generic.Syntax
open import Data.Var
open import Generic.Examples.TypeChecking using (Type); open Type
open import Function

private
  variable
    σ : Type

\end{code}
%<*stlc>
\begin{code}
data `STLC : Set where
  App Lam : Type → Type → `STLC

STLC : Desc Type
STLC = `σ `STLC $ λ where
  (App σ τ) → `X [] (σ `→ τ) (`X [] σ (`∎ τ))
  (Lam σ τ) → `X (σ ∷ []) τ (`∎ (σ `→ τ))
\end{code}
%</stlc>
\begin{code}

\end{code}
%<*patterns>
\begin{code}
pattern `app f t  = `con (App _ _ , f , t , refl)
pattern `lam b    = `con (Lam _ _ , b , refl)
\end{code}
%</patterns>
\begin{code}

\end{code}
%<*identity>
\begin{code}
`id : TM STLC (σ `→ σ)
`id = `lam (`var z)
\end{code}
%</identity>
