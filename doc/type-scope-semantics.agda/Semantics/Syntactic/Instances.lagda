\begin{code}
module Semantics.Syntactic.Instances where

open import Data.List.Base using (List; []; _∷_)
open import Data.Var
open import Data.Environment
open import Syntax.Type
open import Syntax.Calculus
open import Semantics.Specification hiding (module Fundamental)
open import Semantics.Syntactic.Specification
open import Function

private
  variable
   Γ Δ : List Type
   σ : Type

open Syntactic

-- We are, once more, using copatterns to prevent too much unfolding.

\end{code}
%<*synren>
\begin{code}
Syn^Ren : Syntactic Var
Syn^Ren .zro   = z
Syn^Ren .th^𝓣 = th^Var
Syn^Ren .var   = `var
\end{code}
%</synren>


%<*semren>
\begin{code}
Renaming : Semantics Var Term
Renaming = Fundamental.lemma Syn^Ren
\end{code}
%</semren>
%<*ren>
\begin{code}
th^Term : Thinnable (Term σ)
th^Term t ρ = eval Renaming ρ t
\end{code}
%</ren>
%<*synsub>
\begin{code}
Syn^Sub : Syntactic Term
Syn^Sub .zro    = `var z
Syn^Sub .th^𝓣  = th^Term
Syn^Sub .var    = id
\end{code}
%</synsub>
%<*semsub>
\begin{code}
Substitution : Semantics Term Term
Substitution = Fundamental.lemma Syn^Sub
\end{code}
%</semsub>
%<*sub>
\begin{code}
sub : (Γ ─Env) Term Δ → Term σ Γ → Term σ Δ
sub ρ t = eval Substitution ρ t
\end{code}
%</sub>
