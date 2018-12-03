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
    I : Set

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
Name : I ─Scoped
Name σ Γ = String
\end{code}
%</name>
%<*printer>
\begin{code}
Printer : I ─Scoped
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
%<*printingdef>
\begin{code}
Printing : Semantics Name Printer
\end{code}
%</printingdef>
%<*printingvar>
\begin{code}
Printing .th^𝓥 = λ n _ → n
Printing .var   = return
\end{code}
%</printingvar>
%<*printinglam>
\begin{code}
Printing .lam {σ} mb = do
  x ← fresh; b ← mb (bind σ) x
  return $ "λ" ++ x ++ ". " ++ b
\end{code}
%</printinglam>
%<*printingcons>
\begin{code}
Printing .one  = return "<>"
Printing .tt   = return "true"
Printing .ff   = return "false"
\end{code}
%</printingcons>
%<*printingstruct>
\begin{code}
Printing .app mf mt = do
  f ← mf; t ← mt
  return $ f ++ " " ++ parens t
Printing .ifte mb ml mr = do
  b ← mb; l ← ml; r ← mr
  return $  "if " ++ parens b ++
            " then " ++ parens l ++  " else " ++ parens r
\end{code}
%</printingstruct>
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

instance _ = rawIApplicative

\end{code}
%<*print>
\begin{code}
init : M ((Γ ─Env) Name Γ)
init = sequenceA (pack (const fresh))


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
