\begin{code}
module Generic.Examples.TypeChecking where

open import Size
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product as P
open import Data.List hiding ([_])
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Maybe.Categorical as MC

open import Relation.Unary
open import Data.Var hiding (_<$>_)
open import Data.Environment hiding (_<$>_)
open import Generic.Syntax
open import Generic.Semantics

import Category.Monad as CM
import Level
module M = CM.RawMonad (MC.monad {Level.zero})
open M

open import Relation.Binary.PropositionalEquality hiding ([_])

infixr 5 _`→_
\end{code}
%<*type>
\begin{code}
data Type : Set where
  α     : Type
  _`→_  : Type → Type → Type
\end{code}
%</type>
\begin{code}

infix 3 _==_
\end{code}
%<*equal>
\begin{code}
_==_ : (σ τ : Type) → Maybe ⊤
α == α = just tt
(σ₁ `→ τ₁) == (σ₂ `→ τ₂) =
  σ₁ == σ₂ >> τ₁ == τ₂
_ == _ = nothing
\end{code}
%</equal>
%<*arrow>
\begin{code}
isArrow : Type → Maybe (Type × Type)
isArrow (σ `→ τ)  = just (σ , τ)
isArrow α         = nothing
\end{code}
%</arrow>
\begin{code}


\end{code}
%<*constructors>
\begin{code}
data LangC : Set where
  App Lam Emb : LangC
  Cut : Type → LangC
\end{code}
%</constructors>
%<*mode>
\begin{code}
data Mode : Set where
  Check Infer : Mode
\end{code}
%</mode>
%<*bidirectional>
\begin{code}
Lang : Desc Mode
Lang  =  `σ LangC $ λ where
  App      → `X [] Infer (`X [] Check (`∎ Infer))
  Lam      → `X (Infer ∷ []) Check (`∎ Check)
  (Cut σ)  → `X [] Check (`∎ Infer)
  Emb      → `X [] Infer (`∎ Check)
\end{code}
%</bidirectional>
\begin{code}
private
  variable
    Γ Δ : List Mode

pattern `app f t  = `con (App , f , t , refl)
pattern `lam b    = `con (Lam , b , refl)
pattern `cut σ t  = `con (Cut σ , t , refl)
pattern `emb t    = `con (Emb , t , refl)

\end{code}
%<*typemode>
\begin{code}
Type- : Mode → Set
Type- Check  = Type →  Maybe ⊤
Type- Infer  =         Maybe Type
\end{code}
%</typemode>
%<*varmode>
\begin{code}
data Var- : Mode → Set where
  `var : Type → Var- Infer
\end{code}
%</varmode>
\begin{code}
open Semantics

\end{code}
%<*app>
\begin{code}
APP : Type- Infer → Type- Check → Type- Infer
APP f t = do
  σ`→τ     ← f
  (σ , τ)  ← isArrow σ`→τ
  τ <$ t σ
\end{code}
%</app>
%<*lam>
\begin{code}
LAM : Kripke (const ∘ Var-) (const ∘ Type-) (Infer ∷ []) Check Γ → Type- Check
LAM b σ`→τ = do
  (σ , τ) ← isArrow σ`→τ
  b (bind Infer) (ε ∙ `var σ) τ
\end{code}
%</lam>
%<*typecheck>
\begin{code}
Typecheck : Semantics Lang (const ∘ Var-) (const ∘ Type-)
Typecheck .th^𝓥  = th^const
Typecheck .var   = λ where (`var t) → just t
Typecheck .alg   = λ where
   (App , f , t , refl)  → APP f t
   (Lam , b , refl)      → LAM b
   (Cut σ , t , refl)    →  σ <$ t σ
   (Emb , t , refl)      →  λ σ → t >>= σ ==_
\end{code}
%</typecheck>
\begin{code}
private variable m : Mode

\end{code}
%<*typefun>
\begin{code}
type- : ∀ m → TM Lang m → Type- m
type- m t = Semantics.closed Typecheck t
\end{code}
%</typefun>
%<*example>
\begin{code}
_ : let  `id  : TM Lang Check
         `id  = `lam (`emb (`var z))
    in type- Infer (`app (`cut ((α `→ α) `→ (α `→ α)) `id) `id) ≡ just (α `→ α)
_ = refl
\end{code}
%</example>
\begin{code}
