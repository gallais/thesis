\begin{code}
module Semantics.Printing where

open import Size using (∞)
open import Data.List.Base using (List; []; _∷_)
open import Data.Var hiding (_<$>_; get)
open import Data.Environment hiding (_<$>_; _>>_)
open import Syntax.Type
open import Syntax.Calculus
open import Semantics.Specification

open import Function
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Char using (Char)
open import Data.String hiding (show)
open import Data.Nat.Show as NatShow
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)

open import Codata.Thunk
open import Codata.Stream as Stream using (Stream ; head ; tail ; zipWith ; _∷_)
open import Category.Monad.State
open RawIMonadState (StateMonadState (Stream String _)) hiding (zipWith ; pure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    Γ : List Type
    α β σ : Type


\end{code}
%<*monad>
\begin{code}
M : Set → Set
M = State (Stream String ∞)
\end{code}
%</monad>
\begin{code}

\end{code}
%<*name>
\begin{code}
Name : Type ─Scoped
Name σ Γ = String
\end{code}
%</name>
%<*printer>
\begin{code}
Printer : Type ─Scoped
Printer σ Γ = M String
\end{code}
%</printer>
\begin{code}

parens : String → String
parens str = "(" ++ str ++ ")"

open Semantics

\end{code}
%<*fresh>
\begin{code}
fresh : M String
fresh = do
  names ← get
  put (tail names)
  return (head names)
\end{code}
%</fresh>
%<*printing>
\begin{code}
Printing : Semantics Name Printer
\end{code}
Because the output type is not scoped in any way, inning for \AF{Name}s~
(\ARF{th\textasciicircum{}𝓥}) is trivial: we return the same name. The variable~
case (\ARF{var}) is a bit more interesting: after looking up a variable's \AF{Name}~
in the environment, we use \AF{return} to produce the trivial \AF{Printer} constantly~
returning that name.
\begin{code}
Printing .th^𝓥 = λ n _ → n
Printing .var   = return
\end{code}
As often, the case for λ-abstraction (\ARF{lam}) is the most interesting one.~
We first use \AF{fresh} to generate a \AF{Name} for the newly-bound variable,~
then run the printer for the body in the environment extended with that fresh~
name and finally build a string combining the name and the body together.
\begin{code}
Printing .lam {σ} mb = do
  x ← fresh; b ← mb (bind σ) x
  return $ "λ" ++ x ++ ". " ++ b
\end{code}
We then have a collection of base cases for the data constructors of type~
\AIC{`Unit} and \AIC{`Bool}. These give rise to constant printers.
\begin{code}
Printing .one  = return "<>"
Printing .tt   = return "true"
Printing .ff   = return "false"
\end{code}
Finally we have purely structural cases: we run the printers for each of~
the subparts and put the results together, throwing in some extra parenthesis~
to guarantee that the result is unambiguous.
\begin{code}
Printing .app mf mt = do
  f ← mf; t ← mt
  return $ f ++ " " ++ parens t
Printing .ifte mb ml mr = do
  b ← mb; l ← ml; r ← mr
  return $  "if " ++ parens b ++
            " then " ++ parens l ++  " else " ++ parens r
\end{code}
%</printing>
\begin{code}

alphabetWithSuffix : String → List⁺ String
alphabetWithSuffix suffix = List⁺.map (λ c → fromList (c ∷ []) ++ suffix)
                          $′ 'a' ∷ toList "bcdefghijklmnopqrstuvwxyz"

allNats : Stream ℕ _
allNats = Stream.unfold < id , suc > 0

names : Stream String _
names = Stream.concat
      $′ Stream.map alphabetWithSuffix
      $′ "" ∷ λ where .force → Stream.map NatShow.show allNats

\end{code}
%<*print>
\begin{code}
init : M ((Γ ─Env) Name Γ)
init = traverse rawIApplicative (pack (const fresh))

printer : Term σ Γ → M String
printer t = do
  ρ ← init
  Fundamental.lemma Printing ρ t

print : Term σ Γ → String
print t = proj₁ $ printer t names
\end{code}
%</print>

\end{code}
%<*test>
\begin{code}
_ :  print (Term (σ `→ α) (α ∷ β ∷ []) ∋ `lam (`var (s z))) ≡ "λc. a"
_ = refl
\end{code}
%</test>
