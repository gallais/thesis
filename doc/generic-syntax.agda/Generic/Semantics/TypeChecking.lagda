\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Semantics.TypeChecking where

open import Size
open import Function
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Data.List hiding ([_])
open import Data.Maybe using (Maybe; nothing; just)
import Data.Maybe.Categorical as MC

open import Data.Var hiding (_<$>_)
open import Data.Environment hiding (_<$>_)
open import Generic.Syntax
open import Generic.Syntax.Bidirectional; open PATTERNS
open import Generic.Semantics

import Category.Monad as CM
import Level
module M = CM.RawMonad (MC.monad {Level.zero})
open M

open import Relation.Binary.PropositionalEquality hiding ([_])

infix 2 _=?_
\end{code}
%<*typeeq>
\begin{code}
_=?_ : (σ τ : Type) → Maybe ⊤
α         =? α         = just tt
(σ `→ τ)  =? (φ `→ ψ)  = (σ =? φ) >> (τ =? ψ)
_         =? _         = nothing
\end{code}
%</typeeq>
%<*isArrow>
\begin{code}
isArrow : Type → Maybe (Type × Type)
isArrow (σ `→ τ)  = just (σ , τ)
isArrow _         = nothing
\end{code}
%</isArrow>

\begin{code}

private
  variable
    i : Mode
    Γ : List Mode

\end{code}

%<*typemode>
\begin{code}
Type- : Mode → Set
Type- Check  = Type →  Maybe ⊤
Type- Synth  =         Maybe Type
\end{code}
%</typemode>
%<*varmode>
\begin{code}
data Var- : Mode → Set where
  `var : Type → Var- Synth
\end{code}
%</varmode>

%<*app>
\begin{code}
app : Type- Synth → Type- Check → Type- Synth
app f t = do
  arr      ← f
  (σ , τ)  ← isArrow arr
  τ <$ t σ
\end{code}
%</app>
%<*cut>
\begin{code}
cut : Type → Type- Check → Type- Synth
cut σ t = σ <$ t σ
\end{code}
%</cut>
%<*emb>
\begin{code}
emb : Type- Synth → Type- Check
emb t σ = do
  τ ← t
  σ =? τ
\end{code}
%</emb>
%<*lam>
\begin{code}
lam : Kripke (const ∘ Var-) (const ∘ Type-) (Synth ∷ []) Check Γ → Type- Check
lam b arr = do
  (σ , τ) ← isArrow arr
  b (bind Synth) (ε ∙ `var σ) τ
\end{code}
%</lam>

%<*typecheck>
\begin{code}
Typecheck : Semantics Bidi (const ∘ Var-) (const ∘ Type-)
Semantics.th^𝓥  Typecheck = th^const
Semantics.var   Typecheck = λ where (`var σ) → just σ
Semantics.alg   Typecheck = λ where
  (`app' f t)  → app f t
  (`cut' σ t)  → cut σ t
  (`emb' t)    → emb t
  (`lam' b)    → lam b
\end{code}
%</typecheck>

%<*type->
\begin{code}
type- : ∀ mode → TM Bidi mode → Type- mode
type- p = Semantics.closed Typecheck
\end{code}
%</type->
\begin{code}
module _ where

  private β = α `→ α

\end{code}
%<*example>
\begin{code}
  _ : type- Synth (`app (`cut (β `→ β) id^B) id^B) ≡ just β
  _ = refl
\end{code}
%</example>
