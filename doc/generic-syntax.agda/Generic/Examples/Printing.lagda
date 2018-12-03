\begin{code}
module Generic.Examples.Printing where

open import Data.String
open import Data.Bool
open import Data.Product
open import Agda.Builtin.Equality

open import Data.Var
open import Data.Environment
open import Generic.Syntax
open import Generic.Semantics.Printing

open import Generic.Examples.TypeChecking using (Type); open Type
open import Generic.Examples.STLC

private
  variable
    I : Set
    σ : I

\end{code}
%<*display>
\begin{code}
display^STLC : Display STLC
display^STLC = λ where
  (App _ _ , f , t    , _) → "(" ++ f ++ ") " ++ t
  (Lam _ _ , (x , b)  , _) → "λ" ++ lookup x z ++ ". " ++ b
\end{code}
%</display>
%<*example>
\begin{code}
_ :  let f : TM STLC (α `→ α); f = `app `id `id
     in print display^STLC f ≡ "(λa. a) λb. b"
_ = refl
\end{code}
%</example>
