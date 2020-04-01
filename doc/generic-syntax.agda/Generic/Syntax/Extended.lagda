\begin{code}
module Generic.Syntax.Extended where

open import Generic.Syntax
open import Data.Var
open import Data.List.Base
open import Syntax.Type
open import Function

private
  variable
    σ τ : Type

\end{code}
%<*tag:decl>
\begin{code}
data `Term : Set where
\end{code}
%</tag:decl>
%<*tag:lam>
\begin{code}
  Lam : Type → Type → `Term
\end{code}
%</tag:lam>
%<*tag:base>
\begin{code}
  One TT FF : `Term
\end{code}
%</tag:base>
%<*tag:struct>
\begin{code}
  App : Type → Type → `Term
  Ifte : Type → `Term
\end{code}
%</tag:struct>
\begin{code}

\end{code}
%<*term:decl>
\begin{code}
Term : Desc Type
Term = `σ `Term $ λ where
\end{code}
%</term:decl>
%<*term:lam>
\begin{code}
  (Lam σ τ)  → `X (σ ∷ []) τ (`∎ (σ `→ τ))
\end{code}
%</term:lam>
%<*term:base>
\begin{code}
  One        → `∎ `Unit
  TT         → `∎ `Bool
  FF         → `∎ `Bool
\end{code}
%</term:base>
%<*term:struct>
\begin{code}
  (App σ τ)  → `X [] (σ `→ τ) (`X [] σ (`∎ τ))
  (Ifte σ)   → `X [] `Bool (`X [] σ (`X [] σ (`∎ σ)))
\end{code}
%</term:struct>
\begin{code}
