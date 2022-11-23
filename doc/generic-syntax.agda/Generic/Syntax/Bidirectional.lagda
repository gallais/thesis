\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Syntax.Bidirectional where

open import Size
open import Data.Product
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Function

open import Relation.Unary
open import Data.Var
open import Generic.Syntax

infixr 5 _`→_
data Type : Set where
  α : Type
  _`→_ : Type → Type → Type

-- We have an *untyped* language presented in a bidirectional manner
-- where phases are statically checked

\end{code}
%<*mode>
\begin{code}
data Mode : Set where
  Check Synth : Mode
\end{code}
%</mode>
%<*tag>
\begin{code}
data `Bidi : Set where
  App Lam Emb : `Bidi
  Cut : Type → `Bidi
\end{code}
%</tag>
\begin{code}

private
  variable
    m : Mode

-- typesetting only
module TYPESETTING-BIDI where
\end{code}
%<*databidi>
\begin{code}
 data Bidi : Mode ─Scoped where
   `var : ∀[ Var m ⇒ Bidi m ]
   -- choice of four constructors:
   `app : ∀[ Bidi Synth ⇒ Bidi Check ⇒
          Bidi Synth ]
   `lam : ∀[ (Synth ∷_) ⊢ Bidi Check ⇒
          Bidi Check ]
   `cut : Type → ∀[ Bidi Check ⇒ Bidi Synth ]
   `emb : ∀[ Bidi Synth ⇒ Bidi Check ]
\end{code}
%</databidi>

-- On top of the traditional Application and Lambda-Abstraction constructors,
-- we have two change of direction ones: `Emb` which takes inferable terms and
-- makes them checkable (it is enough to compare the inferred type to the
-- candidate provided); and `Cut` which takes a checkable term and makes it
-- inferrable thanks to a type-annotation.

\end{code}
%<*desc>
\begin{code}
Bidi : Desc Mode
Bidi  =  `σ `Bidi $ λ where
  -- var will be freely adjoined
  App      → `X [] Synth (`X [] Check
             (`∎ Synth))
  Lam      → `X (Synth ∷ []) Check
             (`∎ Check)
  (Cut σ)  → `X [] Check (`∎ Synth)
  Emb      → `X [] Synth (`∎ Check)
\end{code}
%</desc>
\begin{code}

module PATTERNS where


  pattern `app' f t  = (App , f , t , refl)
  pattern `lam' b    = (Lam , b , refl)
  pattern `cut' σ t  = (Cut σ , t , refl)
  pattern `emb' t    = (Emb , t , refl)

  pattern `app f t  = `con (`app' f t)
  pattern `lam b    = `con (`lam' b)
  pattern `cut σ t  = `con (`cut' σ t)
  pattern `emb t    = `con (`emb' t)

\end{code}

%<*BDid>
\begin{code}
id^B : TM Bidi Check
id^B = `lam (`emb (`var z))
\end{code}
%</BDid>
\begin{code}
  where open PATTERNS
\end{code}
