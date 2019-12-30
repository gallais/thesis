\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Semantics.Printing where

open import Size using (∞)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Var hiding (_<$>_; get)
open import Data.Environment hiding (_<$>_; _>>_)
open import Syntax.Type
open import Syntax.Calculus
open import Semantics.Specification

open import Function
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Char using (Char)
open import Data.String using (String; _++_; concat; fromList; toList)
open import Data.Nat.Show as NatShow
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)

open import Codata.Thunk
open import Codata.Stream as Stream using (Stream ; head ; tail ; zipWith ; _∷_)
open import Category.Monad.State
open RawIMonadState (StateMonadState (Stream String _)) hiding (zipWith ; pure)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    I : Set
    Γ Δ : List I
    α β σ τ : I
    A B : Set

\end{code}
%<*monad>
\begin{code}
Fresh : Set → Set
Fresh = State (Stream String ∞)
\end{code}
%</monad>

%<*valprint>
\begin{code}
record Wrap A (σ : I) (Γ : List I) : Set where
  constructor MkW; field getW : A
\end{code}
%</valprint>
\begin{code}
open Wrap public

th^Wrap : Thinnable {I} (Wrap A σ)
th^Wrap w ρ = MkW (getW w)

map^Wrap : (A → B) → ∀[ Wrap A σ ⇒ Wrap B σ ]
map^Wrap f (MkW a) = MkW (f a)

reindex^Wrap : Wrap A σ Γ → Wrap A τ Δ
reindex^Wrap (MkW w) = MkW w
\end{code}
%<*name>
\begin{code}
Name : I ─Scoped
Name = Wrap String
\end{code}
%</name>
%<*printer>
\begin{code}
Printer : I ─Scoped
Printer = Wrap (Fresh String)
\end{code}
%</printer>
\begin{code}

parens : String → String
parens str = "(" ++ str ++ ")"

unwords : List String → String
unwords = concat ∘ List.intersperse " "

\end{code}
%<*fresh>
\begin{code}
fresh : ∀ σ → Fresh (Name σ (σ ∷ Γ))
fresh σ = do
  names ← get
  put (tail names)
  return (MkW (head names))
\end{code}
%</fresh>

%<*semprint>
\begin{code}
Printing : Semantics Name Printer
Printing = record { th^𝓥 = th^Wrap; var = var; app = app; lam = lam
                  ; one = one; tt = tt; ff = ff; ifte = ifte }
\end{code}
%</semprint>
\begin{code}
  where
\end{code}
%<*printvar>
\begin{code}
  var : ∀[ Name σ ⇒ Printer σ ]
  var = map^Wrap return
\end{code}
%</printvar>
%<*printlam>
\begin{code}
  lam : ∀[ □ (Name σ ⇒ Printer τ) ⇒ Printer (σ `→ τ) ]
  lam {σ} mb = MkW do
    x ← fresh σ
    b ← getW (mb extend x)
    return ("λ" ++ getW x ++ ". " ++ b)
\end{code}
%</printlam>
%<*printcons>
\begin{code}
  one : ∀[ Printer `Unit ]
  one = MkW (return "()")

  tt : ∀[ Printer `Bool ]
  tt = MkW (return "true")

  ff : ∀[ Printer `Bool ]
  ff = MkW (return "false")
\end{code}
%</printcons>
%<*printstruct>
\begin{code}
  app : ∀[ Printer (σ `→ τ) ⇒ Printer σ ⇒ Printer τ ]
  app mf mt = MkW do
    f ← getW mf
    t ← getW mt
    return (f ++ parens t)

  ifte : ∀[ Printer `Bool ⇒ Printer σ ⇒ Printer σ ⇒ Printer σ ]
  ifte mb ml mr = MkW do
    b ← getW mb
    l ← getW ml
    r ← getW mr
    return (unwords ("if" ∷ parens b  ∷ "then" ∷ parens l
                                      ∷ "else" ∷ parens r ∷ []) )
\end{code}
%</printstruct>
\begin{code}

alphabetWithSuffix : String → List⁺ String
alphabetWithSuffix suffix = List⁺.map (λ c → fromList (c ∷ []) ++ suffix)
                          $′ 'a' ∷ toList "bcdefghijklmnopqrstuvwxyz"

allNats : Stream ℕ _
allNats = Stream.iterate suc 0

names : Stream String _
names = Stream.concat
      $′ Stream.map alphabetWithSuffix
      $′ "" ∷ λ where .force → Stream.map NatShow.show allNats

instance _ = rawIApplicative

\end{code}
%<*printclosed>
\begin{code}
print : ∀ σ → Term σ [] → String
print σ t = proj₁ (getW printer names) where

  printer : Printer σ []
  printer = Fundamental.lemma Printing ε t
\end{code}
%</printclosed>
%<*test>
\begin{code}
_ :  print (σ `→ σ) (`lam (`var z)) ≡ "λa. a"
_ = refl
\end{code}
%</test>
