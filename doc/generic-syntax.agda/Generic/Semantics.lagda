\begin{code}

module Generic.Semantics {I : Set} where

open import Size
open import Data.List.Base as L hiding (lookup ; [_])

open import Data.Var hiding (z; s)
open import Data.Relation
open import Relation.Unary
open import Data.Environment
open import Generic.Syntax

private
  variable
    σ : I
    Γ Δ : List I
    s : Size

module _  {d : Desc I} where

\end{code}
%<*comp>
\begin{code}
 _─Comp : List I → I ─Scoped → List I → Set
 (Γ ─Comp) 𝓒 Δ = ∀ {s σ} → Tm d s σ Γ → 𝓒 σ Δ
\end{code}
%</comp>
%<*semrec>
\begin{code}
record Semantics (d : Desc I) (𝓥 𝓒 : I ─Scoped) : Set where
\end{code}
%</semrec>
\begin{code}
 field
\end{code}
%<*thv>
\begin{code}
   th^𝓥 : Thinnable (𝓥 σ)
\end{code}
%</thv>
%<*var>
\begin{code}
   var : ∀[ 𝓥 σ ⇒ 𝓒 σ ]
\end{code}
%</var>
%<*alg>
\begin{code}
   alg : ∀[ ⟦ d ⟧ (Kripke 𝓥 𝓒) σ ⇒ 𝓒 σ ]
\end{code}
%</alg>
%<*semtype>
\begin{code}
 sem   : (Γ ─Env) 𝓥 Δ → (Γ ─Comp) 𝓒 Δ
 body  : (Γ ─Env) 𝓥 Δ → ∀ Θ σ → Scope (Tm d s) Θ σ Γ → Kripke 𝓥 𝓒 Θ σ Δ
\end{code}
%</semtype>
%<*semproof>
\begin{code}
 sem ρ (`var k) = var (lookup ρ k)
 sem ρ (`con t) = alg (fmap d (body ρ) t)
\end{code}
%</semproof>
%<*bodyproof>
\begin{code}
 body ρ []       i t = sem ρ t
 body ρ (_ ∷ _)  i t = λ σ vs → sem (vs >> th^Env th^𝓥 ρ σ) t
\end{code}
%</bodyproof>
\begin{code}
 closed : ([] ─Comp) 𝓒 []
 closed = sem ε
\end{code}
