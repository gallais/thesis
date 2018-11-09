\begin{code}
module Semantics.Syntactic.Specification where

open import Data.List.Base using (List; []; _∷_)
open import Syntax.Type
open import Syntax.Calculus
open import Data.Var
open import Data.Environment
open import Semantics.Specification as Semantics hiding (module Fundamental)
open import Relation.Unary

private
  variable
    σ : Type
    Γ : List Type
    𝓣 : Type ─Scoped
\end{code}
%<*syntactic>
\begin{code}
record Syntactic (𝓣 : Type ─Scoped) : Set where
  field  zro   : ∀[ (σ ∷_) ⊢ 𝓣 σ ]
         th^𝓣  : Thinnable (𝓣 σ)
         var   : ∀[ 𝓣 σ ⇒ Term σ ]
\end{code}
%</syntactic>
\begin{code}

-- Using copatterns in the definition of syntactic guarantees that these things are
-- not unfolded when normalising goals thus making them more readable.
\end{code}
%<*syntacticsem>
\begin{code}
module Fundamental (𝓢 : Syntactic 𝓣) where

  open Syntactic 𝓢

  syntactic : Semantics 𝓣 Term
  Semantics.th^𝓥  syntactic = th^𝓣
  Semantics.var   syntactic = var
  Semantics.lam   syntactic = λ b → `lam (b extend zro)
  Semantics.app   syntactic = `app
  Semantics.one   syntactic = `one
  Semantics.tt    syntactic = `tt
  Semantics.ff    syntactic = `ff
  Semantics.ifte  syntactic = `ifte
\end{code}
%</syntacticsem>
