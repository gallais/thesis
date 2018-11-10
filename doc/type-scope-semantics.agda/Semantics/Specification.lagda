\begin{code}
module Semantics.Specification where

open import Syntax.Type
open import Syntax.Calculus
open import Data.Var
open import Data.Environment hiding (Kripke)
open import Data.List using (List; []; _∷_)
open import Relation.Unary

private

  variable
    σ τ : Type
    Γ Δ : List Type
    𝓥 𝓒 : Type ─Scoped

\end{code}
%<*comp>
\begin{code}
_─Comp : List Type → Type ─Scoped → List Type → Set
(Γ ─Comp) 𝓒 Δ = ∀ {σ} → Term σ Γ → 𝓒 σ Δ
\end{code}
%</comp>

%<*kripke>
\begin{code}
Kripke : (𝓥 𝓒 : Type ─Scoped) → Type → Type → List Type → Set
Kripke 𝓥 𝓒 σ τ Γ = ∀[ Thinning Γ ⇒ 𝓥 σ ⇒ 𝓒 τ ]
\end{code}
%</kripke>
%<*semantics>
\begin{code}
record Semantics (𝓥 𝓒 : Type ─Scoped) : Set where
  field
\end{code}
The first method of a \AR{Semantics} deals with environment values. They~
need to be thinnable (\ARF{th\textasciicircum{}𝓥}) so that the traversal~
may introduce fresh variables when going under a binder whilst keeping~
the environment well-scoped.
\begin{code}
    th^𝓥   :  Thinnable (𝓥 σ)
\end{code}
The structure of the model is quite constrained: each constructor~
in the language needs a semantic counterpart. We start with the~
two most interesting cases: \ARF{var} and \ARF{lam}. The variable~
case bridges the gap between the fact that the environment translates~
variables into values \AB{𝓥} but the evaluation function returns~
computations \AB{𝓒}.
\begin{code}
    var    :  ∀[ 𝓥 σ ⇒ 𝓒 σ ]
\end{code}
The semantic λ-abstraction is notable for two reasons: first, following~
Mitchell and Moggi~(\citeyear{mitchell1991kripke}), its \AF{□}-structure is~
typical of models à la Kripke allowing arbitrary extensions of the context;~
and second, instead of being a function in the host language taking~
computations to computations,  it takes \emph{values} to computations.~
It matches precisely the fact that the body of a λ-abstraction exposes~
one extra free variable, prompting us to extend the environment with a~
value for it. In the special case where \AB{𝓥} = \AB{𝓒} (normalisation~
by evaluation for instance), we recover the usual Kripke structure.
\begin{code}
    lam    :  ∀[ □ (𝓥 σ ⇒ 𝓒 τ) ⇒ 𝓒 (σ `→ τ) ]
\end{code}
The remaining fields' types are a direct translation of the types
of the constructor they correspond to: substructures have simply
been replaced with computations thus making these operators ideal
to combine induction hypotheses.
\begin{code}
    app    :  ∀[ 𝓒 (σ `→ τ) ⇒ 𝓒 σ ⇒ 𝓒 τ ]
    one    :  ∀[ 𝓒 `Unit ]
    tt     :  ∀[ 𝓒 `Bool ]
    ff     :  ∀[ 𝓒 `Bool ]
    ifte   :  ∀[ 𝓒 `Bool ⇒ 𝓒 σ ⇒ 𝓒 σ ⇒ 𝓒 σ ]
\end{code}
%</semantics>
\begin{code}
Evaluation : (𝓥 𝓒 : Type ─Scoped) → Set
Evaluation 𝓥 𝓒 = ∀ {Γ Δ} → (Γ ─Env) 𝓥 Δ → (Γ ─Comp) 𝓒 Δ

Evaluation' : (𝓒 :  Type ─Scoped) → Set
Evaluation' 𝓒 = ∀ {Γ} → (Γ ─Comp) 𝓒 Γ

\end{code}
%<*fundamental>
\begin{code}
module Fundamental (𝓢 : Semantics 𝓥 𝓒) where
  open Semantics 𝓢

  lemma : (Γ ─Env) 𝓥 Δ → (Γ ─Comp) 𝓒 Δ
  lemma ρ (`var v)       = var (lookup ρ v)
  lemma ρ (`app t u)     = app (lemma ρ t) (lemma ρ u)
  lemma ρ (`lam t)       = lam (λ re u → lemma (th^Env th^𝓥 ρ re ∙ u) t)
  lemma ρ `one           = one
  lemma ρ `tt            = tt
  lemma ρ `ff            = ff
  lemma ρ (`ifte b l r)  = ifte (lemma ρ b) (lemma ρ l) (lemma ρ r)
\end{code}
%</fundamental>
\begin{code}

--  lemma' : Evaluation' 𝓒
--  lemma' t = lemma (pack embed) t
\end{code}
