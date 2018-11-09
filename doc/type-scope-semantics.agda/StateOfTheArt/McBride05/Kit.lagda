\begin{code}
module StateOfTheArt.McBride05.Kit where

open import Data.List hiding ([_]; lookup)
open import Data.Var hiding (_<$>_)
open import Data.Environment
open import Relation.Unary
open import Function
open import StateOfTheArt.McBride05.Base using (Type; Tm)
open Type
open Tm

private
  variable
    σ τ : Type
    Γ Δ : List Type
    ⧫   : Type ─Scoped

\end{code}
%<*kitdef>
\begin{code}
record Kit (⧫ : Type ─Scoped) : Set where
  field  var  : ∀[ ⧫ σ ⇒ Tm σ ]
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
kit K ρ (`var v)    = K .var (lookup ρ v)
kit K ρ (`app f t)  = `app (kit K ρ f) (kit K ρ t)
kit K ρ (`lam b)    = `lam (kit K ρ′ b)
  where ρ′ =  (K .wkn <$> ρ) ∙ K .zro
\end{code}
%</kitsem>

%<*renkit>
\begin{code}
ren^Kit : Kit Var
ren^Kit .var = `var
ren^Kit .zro = z
ren^Kit .wkn = s
\end{code}
%</renkit>

%<*ren>
\begin{code}
ren : Thinning Γ Δ → Tm σ Γ → Tm σ Δ
ren = kit ren^Kit
\end{code}
%</ren>

%<*subkit>
\begin{code}
sub^Kit : Kit Tm
sub^Kit .var = id
sub^Kit .zro = `var z
sub^Kit .wkn = ren (pack s)
\end{code}
%</subkit>
%<*sub>
\begin{code}
sub : (Γ ─Env) Tm Δ → Tm σ Γ → Tm σ Δ
sub = kit sub^Kit
\end{code}
%</sub>
\begin{code}


Val : Type ─Scoped
Val base      Γ = Tm base Γ
Val (arr σ τ) Γ = ∀ {Δ} → Thinning Γ Δ → Val σ Δ → Val τ Δ

th^Val : ∀ {σ} → Thinning Γ Δ → Val σ Γ → Val σ Δ
th^Val {σ = base   } ρ v = ren ρ v
th^Val {σ = arr σ τ} ρ v = v ∘ (select ρ)

APP : Val (arr σ τ) Γ →  Val σ Γ → Val τ Γ
APP f t = f (pack id) t

LAM : Val (arr σ τ) Γ → Val (arr σ τ) Γ
LAM = id
\end{code}
%<*nbe>
\begin{code}
nbe : (Γ ─Env) Val Δ → Tm σ Γ → Val σ Δ
nbe ρ (`var v)    = lookup ρ v
nbe ρ (`app f t)  = APP (nbe ρ f) (nbe ρ t)
nbe ρ (`lam t)    = LAM (λ re v → nbe ((th^Val re <$> ρ) ∙ v) t)
\end{code}
%</nbe>
