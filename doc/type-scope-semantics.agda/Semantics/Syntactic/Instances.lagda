\begin{code}
module Semantics.Syntactic.Instances where

open import Data.List.Base using (List; []; _∷_)
open import Data.Var
open import Data.Environment
open import Syntax.Type
open import Syntax.Calculus
open import Semantics.Specification
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

%<*ren>
\begin{code}
th^Term : Thinnable (Term σ)
th^Term t ρ =  let Sem^Ren = Fundamental.syntactic Syn^Ren
               in Fundamental.lemma Sem^Ren ρ t
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
%<*sub>
\begin{code}
sub : (Γ ─Env) Term Δ → Term σ Γ → Term σ Δ
sub ρ t =  let Sem^Sub = Fundamental.syntactic Syn^Sub
           in Fundamental.lemma Sem^Sub ρ t
\end{code}
%</sub>
