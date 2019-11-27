\begin{code}
{-# OPTIONS --safe --sized-types #-}

module Generic.Semantics.Printing {I : Set} where

open import Codata.Stream using (Stream)
open import Size
open import Data.Product
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.String using (String)
open import Category.Monad
open import Category.Monad.State
open import Function
open import Relation.Unary

-- We reuse Name, Printer, M, fresh, and names from the STLC printing example

open import Semantics.Printing
  using (Fresh; Wrap; Name; Printer; MkW; getW; map^Wrap; th^Wrap; fresh; names)

private
  variable
    Γ Δ : List I
    σ : I
    i : Size

-- The Printing Monad we are working with: a state containing a stream
-- of *distinct* Strings.
module ST = RawMonadState (StateMonadState (Stream String _))
open ST renaming (rawIApplicative to ApplicativeM)
        hiding (_<$>_)

open import Data.Var hiding (get; _<$>_)
open import Data.Environment hiding (_>>_; sequenceA; _<$>_)
open import Data.Var.Varlike
open import Generic.Syntax hiding (sequenceA)
open import Generic.Semantics

\end{code}
%<*vlmname>
\begin{code}
vl^FreshName : VarLike (λ (σ : I) → Fresh ∘ (Name σ))
vl^FreshName = record
  { th^𝓥  = th^Functor functor^M th^Wrap
  ; new   = fresh _
  }
\end{code}
%</vlmname>
\begin{code}
    where open ST renaming (rawFunctor to functor^M)

-- To print a term the user need to explain to us how to display one
-- layer of term given that the newly-bound variables have been assigned
-- fresh names and the subterms have already been rendered using these
-- names.

\end{code}
%<*pieces>
\begin{code}
Pieces : List I → I ─Scoped
Pieces []  i Γ = String
Pieces Δ   i Γ = (Δ ─Env) Name (Δ ++ Γ) × String
\end{code}
%</pieces>
%<*reifytype>
\begin{code}
reify^Pieces : ∀ Δ i → Kripke Name Printer Δ i Γ → Fresh (Pieces Δ i Γ)
\end{code}
%</reifytype>
%<*reifybase>
\begin{code}
reify^Pieces []         i p  = getW p
\end{code}
%</reifybase>
%<*reifypieces>
\begin{code}
reify^Pieces Δ@(_ ∷ _)  i f  = do
  ρ ← sequenceA (freshˡ vl^FreshName _)
  b ← getW (f (freshʳ vl^Var Δ) ρ)
  return (ρ , b)
\end{code}
%</reifypieces>
\begin{code}
  where open Data.Environment
        instance _ = ApplicativeM

\end{code}
%<*display>
\begin{code}
Display : Desc I → Set
Display d = ∀ {i Γ} → ⟦ d ⟧ Pieces i Γ → String
\end{code}
%</display>
\begin{code}

---------------------------------------------------------------------
-- Generic Printing Semantics

-- Given a strategy to `Display` one layer of term we can generate a full
-- printer.

open Semantics

module _ {d : Desc I} where

\end{code}
%<*printing>
\begin{code}
  Printing : Display d → Semantics d Name Printer
  Printing dis .th^𝓥  = th^Wrap
  Printing dis .var   = map^Wrap return
  Printing dis .alg   = λ v → MkW $ dis <$> mapA d reify^Pieces v
\end{code}
%</printing>
\begin{code}
    where open Generic.Syntax
          open ST
          instance _ = ApplicativeM

-- Corollary: a generic printer using a silly name supply


  open Data.Environment
  instance _ = ApplicativeM

\end{code}
%<*print>
\begin{AgdaAlign}
\AgdaNoSpaceAroundCode
%<*printtype>
\begin{code}
  print : Display d → Tm d i σ Γ → String
\end{code}
%</printtype>
\begin{AgdaSuppressSpace}
\begin{code}
  print dis t = proj₁ (printer names) where
    printer : Fresh String
    printer = do
      init ← sequenceA (base vl^FreshName)
      getW (Semantics.semantics (Printing dis) init t)
\end{code}
\AgdaSpaceAroundCode
\end{AgdaSuppressSpace}
\end{AgdaAlign}
%</print>
\begin{code}
