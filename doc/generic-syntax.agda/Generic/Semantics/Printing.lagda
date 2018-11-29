\begin{code}
module Generic.Semantics.Printing {I : Set} where

open import Codata.Thunk using (Thunk; force)
open import Codata.Stream as Stream using (Stream; _∷_)

open import Data.Product
open import Data.Nat.Base
open import Data.Nat.Show as Nat
open import Data.List.Base using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Char
open import Data.String using (String ; _++_ ; fromList ; toList)
open import Category.Monad
open import Category.Monad.State
open import Function
open import Relation.Unary

private
  variable
    Γ Δ : List I
    σ : I

-- The Printing Monad we are working with: a state containing a stream
-- of *distinct* Strings.
module ST = RawMonadState (StateMonadState (Stream String _))
M = State (Stream String _)
open ST renaming (rawIApplicative to ApplicativeM)
        hiding (_<$>_)

open import Data.Var hiding (get; _<$>_)
open import Data.Environment hiding (_>>_)
open import Data.Var.Varlike
open import Generic.Syntax as Syntax hiding (traverse)
open import Generic.Semantics

-- First we use some wrappers with phantom indices for the type of
-- Values and Computations of our Semantics
\end{code}
%<*name>
\begin{code}
Name : I ─Scoped
Name _ _ = String
\end{code}
%</name>
%<*printer>
\begin{code}
Printer : I ─Scoped
Printer _ _ = M String
\end{code}
%</printer>
\begin{code}

-- We define a handy combinator to generate fresh Names (and make sure
-- they are dropped from the state)

fresh : M String
fresh = do
  nms ← get
  put (Stream.tail nms)
  return $ Stream.head nms

-- Names are varlike in the monad M: we use the state to generate fresh
-- ones. Closure under thinning is a matter of wrapping / unwrapping the
-- name.

\end{code}
%</name>
%<*vlMName>
\begin{code}
vl^MName : VarLike (λ i Γ → M (Name i Γ))
new   vl^MName = fresh
th^𝓥 vl^MName = th^const
\end{code}
%</vlMName>
\begin{code}


-- To print a term the user need to explain to us how to display one
-- layer of term given that the newly-bound variables have been assigned
-- fresh names and the subterms have already been rendered using these
-- names.

\end{code}
%<*pieces>
\begin{code}
Pieces : List I → I ─Scoped
Pieces []  i Γ = String
Pieces Δ   i Γ = (Δ ─Env) Name [] × String
\end{code}
%</pieces>
%<*reifypieces>
\begin{code}
reify^M : ∀ Δ i → Kripke Name Printer Δ i Γ → M (Pieces Δ i Γ)
reify^M []         i    = id
reify^M Δ@(_ ∷ _)  i f  = do
  ρ ← traverse ApplicativeM (freshˡ vl^MName _)
  b ← f (freshʳ vl^Var Δ) ρ
  return ((id <$> ρ) , b)
\end{code}
%</reifypieces>
\begin{code}

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
%<*printings>
\begin{code}
  printing : Display d → Semantics d Name Printer
  printing dis .th^𝓥  n = const $ n
  printing dis .var    n = return n
  printing dis .alg    v =
    dis ST.<$> Syntax.traverse ApplicativeM d (fmap d reify^M v)
\end{code}
%</printing>
\begin{code}

-- Corollary: a generic printer using a silly name supply

  print : Display d → {i : I} → TM d i → String
  print dis t = proj₁ $ closed (printing dis) t names where

    alphabetWithSuffix : String → List⁺ String
    alphabetWithSuffix suffix = List⁺.map (λ c → fromList (c ∷ []) ++ suffix)
                              $′ 'a' ∷ toList "bcdefghijklmnopqrstuvwxyz"

    allNats : Stream ℕ _
    allNats = Stream.unfold < id , suc > 0

    names : Stream String _
    names = Stream.concat
          $′ Stream.map alphabetWithSuffix
          $′ "" ∷ λ where .force → Stream.map Nat.show allNats
