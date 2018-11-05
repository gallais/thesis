\begin{code}
module StateOfTheArt.McBride05 where

open import Data.List hiding ([_]; lookup)
open import Data.Var
open import Data.Environment as E
open import Relation.Unary
open import Function

data Type : Set where
  base : Type
  arr  : Type → Type → Type

private
  variable
    σ τ ν : Type
    Γ Δ Θ : List Type
    ⧫     : Type ─Scoped

data Tm : Type ─Scoped where
  `var : ∀[ Var σ               ⇒ Tm σ         ]
  _`$_ : ∀[ Tm (arr σ τ) ⇒ Tm σ ⇒ Tm τ         ]
  `λ   : ∀[ (σ ∷_) ⊢ Tm τ       ⇒ Tm (arr σ τ) ]
\end{code}
%<*ren>
\begin{code}
ren : (Γ ─Env) Var Δ → Tm σ Γ → Tm σ Δ
ren ρ (`var v)  = `var (lookup ρ v)
ren ρ (f `$ t)  = ren ρ f `$ ren ρ t
ren ρ (`λ b)    = `λ (ren (lift ρ) b)
\end{code}
%</ren>
\begin{code}
  where

  lift : (Γ ─Env) Var Δ → ((σ ∷ Γ) ─Env) Var (σ ∷ Δ)
  lift ρ = th^Env th^Var ρ extend ∙ z

\end{code}
%<*sub>
\begin{code}
sub : (Γ ─Env) Tm Δ → Tm σ Γ → Tm σ Δ
sub ρ (`var v)  = lookup ρ v
sub ρ (f `$ t)  = sub ρ f `$ sub ρ t
sub ρ (`λ b)    = `λ (sub (lift ρ) b)
\end{code}
%</sub>
\begin{code}
  where

  lift : (Γ ─Env) Tm Δ → ((σ ∷ Γ) ─Env) Tm (σ ∷ Δ)
  lift ρ = th^Env (λ t ρ → ren ρ t) ρ extend ∙ `var z

\end{code}
%<*kitdef>
\begin{code}
record Kit (⧫ : Type ─Scoped) : Set where
  field
    var  : ∀[ ⧫ σ ⇒ Tm σ ]
    zro  : ∀[ (σ ∷_) ⊢ ⧫ σ ]
    wkn  : ∀[ ⧫ τ ⇒ (σ ∷_) ⊢ ⧫ τ ]
\end{code}
%</kitdef>
\begin{code}

open Kit

\end{code}
%<*kitsem>
\begin{code}
kit : Kit ⧫ → (Γ ─Env) ⧫ Δ → Tm σ Γ → Tm σ Δ
kit K ρ (`var v)  = K .var (lookup ρ v)
kit K ρ (f `$ t)  = kit K ρ f `$ kit K ρ t
kit K ρ (`λ b)    = `λ (kit K (lift K ρ) b)
\end{code}
%</kitsem>
\begin{code}
  where

  lift : Kit ⧫ → (Γ ─Env) ⧫ Δ → ((σ ∷ Γ) ─Env) ⧫ (σ ∷ Δ)
  lift K ρ =  K .wkn E.<$> ρ ∙ K .zro

Val : Type ─Scoped
Val base      Γ = Tm base Γ
Val (arr σ τ) Γ = ∀ {Δ} → Thinning Γ Δ → Val σ Δ → Val τ Δ

th^Val : ∀ σ → Thinnable (Val σ)
th^Val base      v ρ = ren ρ v
th^Val (arr σ τ) v ρ = v ∘ (select ρ)

APP : Val (arr σ τ) Γ →  Val σ Γ → Val τ Γ
APP f t = f (pack id) t

LAM : Val (arr σ τ) Γ → Val (arr σ τ) Γ
LAM = id
\end{code}
%<*nbe>
\begin{code}
nbe : (Γ ─Env) Val Δ → Tm σ Γ → Val σ Δ
nbe ρ (`var v)  = lookup ρ v
nbe ρ (f `$ t)  = APP (nbe ρ f) (nbe ρ t)
nbe ρ (`λ t)    = LAM (λ re v → nbe (lift ρ re v) t)
\end{code}
%</nbe>
\begin{code}
  where

  lift : (Γ ─Env) Val Δ → Thinning Δ Θ → Val σ Θ → ((σ ∷ Γ) ─Env) Val Θ
  lift ρ re v = th^Env (th^Val _) ρ re ∙ v
\end{code}
