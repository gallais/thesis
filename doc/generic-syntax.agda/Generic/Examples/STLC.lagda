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
open import Relation.Unary

private
  variable
    σ τ : Type


-- typesetting only
module TYPESETTING-STLC where
\end{code}
%<*datastlc>
\begin{code}
 data STLC : Type ─Scoped where
   `var : ∀[ Var σ ⇒ STLC σ ]
   -- choice of two constructors:
   `app : ∀[ STLC (σ `→ τ) ⇒
          STLC σ ⇒ STLC τ ]
   `lam : ∀[ (σ ∷_) ⊢ STLC τ ⇒ STLC (σ `→ τ) ]
\end{code}
%</datastlc>

\end{code}
%<*tag>
\begin{code}
data `STLC : Set where
  App Lam : Type → Type → `STLC
\end{code}
%</tag>

%<*stlc>
\begin{code}
STLC : Desc Type
-- var will be freely adjoined
STLC = `σ `STLC $ λ where
  (App σ τ) → `X [] (σ `→ τ)
              (`X [] σ (`∎ τ))
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
id^S : TM STLC (σ `→ σ)
id^S = `lam (`var z)
\end{code}
%</identity>
