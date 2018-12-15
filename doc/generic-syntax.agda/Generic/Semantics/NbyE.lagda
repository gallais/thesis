\begin{code}
module Generic.Semantics.NbyE  {I : Set} where

import Level
open import Size
import Category.Monad as CM
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.List.Base hiding ([_])
open import Data.Maybe.Base
import Data.Maybe.Categorical as MC
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Relation.Unary
open import Data.Var hiding (_<$>_)
open import Data.Var.Varlike
open import Data.Environment hiding (sequenceA; _<$>_)
open import Generic.Syntax
open import Generic.Semantics

private
  variable
    σ : I
    i : Size

\end{code}
%<*domain>
\begin{code}
{-# NO_POSITIVITY_CHECK #-}
data Dm (d : Desc I) : Size → I ─Scoped where
  V : ∀[ Var σ                               ⇒  Dm d i      σ ]
  C : ∀[ ⟦ d ⟧ (Kripke (Dm d i) (Dm d i)) σ  ⇒  Dm d (↑ i)  σ  ]
  ⊥ : ∀[                                        Dm d (↑ i)  σ  ]
\end{code}
%</domain>
\begin{code}
module _ {d : Desc I} where

\end{code}
%<*thdm>
\begin{code}
 th^Dm : Thinnable (Dm d i σ)
 th^Dm (V k)  ρ = V (th^Var k ρ)
 th^Dm (C t)  ρ = C (fmap d (λ Θ i kr → th^Kr Θ th^Dm kr ρ) t)
 th^Dm ⊥      ρ = ⊥
\end{code}
%</thdm>
\begin{code}
 vl^Dm : VarLike (Dm d i)
 vl^Dm = record { new = V z ; th^𝓥 = th^Dm }

 module M = CM.RawMonad (MC.monad {Level.zero})
 open M renaming (rawIApplicative to ApplicativeMaybe)
 instance _ = ApplicativeMaybe
\end{code}
%<*reify>
\begin{code}
 reify^Dm  : ∀[ Dm d i σ ⇒ Maybe ∘ Tm d ∞ σ ]
 reify^Dm ⊥      = nothing
 reify^Dm (V k)  = just (`var k)
 reify^Dm (C v)  = `con <$> sequenceA d (fmap d reify^Kripke v)
   where reify^Kripke = λ Θ i kr → reify^Dm (reify vl^Dm Θ i kr)
\end{code}
%</reify>
\begin{code}
open Semantics
private
  variable
    d : Desc I

\end{code}
%<*alg>
\begin{code}
Alg : Desc I → Set
Alg d = ∀ {σ} → ∀[ ⟦ d ⟧ (Kripke (Dm d ∞) (Dm d ∞)) σ ⇒ Dm d ∞ σ ]
\end{code}
%</alg>
%<*nbe>
\begin{code}
nbe : Alg d → Semantics d (Dm d ∞) (Dm d ∞)
nbe alg .th^𝓥  = th^Dm
nbe alg .var   = id
nbe alg .alg   = alg
\end{code}
%</nbe>
%<*norm>
\begin{code}
norm : Alg d → ∀[ Tm d ∞ σ ⇒ Maybe ∘ Tm d ∞ σ ]
norm alg t = reify^Dm (semantics (nbe alg) (base vl^Dm) t)
\end{code}
%</norm>
