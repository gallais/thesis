\begin{code}
module Generic.Examples.NbyE where

open import Size
open import Data.Maybe
open import Data.Bool
open import Data.Product
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Function

open import Relation.Unary
open import Data.Var.Varlike
open import Data.Environment
open import Generic.Syntax
import Generic.Semantics.NbyE as NbyE
open NbyE hiding (norm)

open import Generic.Examples.UntypedLC

-- Normalization by Evaluation for the Untyped Lambda Calculus

-- * A Lambda is Already a Value
-- * An Application can behave in two different ways:
--   1. if the function is a lambda then it reduces
--   2. Otherwise the spine of eliminators grows

\end{code}
%<*norm>
\begin{code}
norm : ∀[ Tm UTLC ∞ _ ⇒ Maybe ∘ Tm UTLC ∞ _ ]
norm = NbyE.norm $ λ where
  (false , b)                         → C (false , b)
  (true , C (false , b , _) , t , _)  → b (base vl^Var) (ε ∙ t)
  (true , ft)                         → C (true , ft)

\end{code}
%</norm>
%<*example>
\begin{code}
_ : norm (`app `id (`app `id `id)) ≡ just `id
_ = refl
\end{code}
%</example>
