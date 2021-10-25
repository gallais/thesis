\begin{code}
module Generic.Examples.UntypedLC where

open import Size
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.List.Base hiding ([_])
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Relation.Unary
open import Data.Var
open import Generic.Syntax

\end{code}
%<*ulc>
\begin{code}
UTLC : Desc ⊤
UTLC = `σ Bool $ λ isApp → if isApp
  then  `X [] tt (`X [] tt (`∎ tt))
  else  `X (tt ∷ []) tt (`∎ tt)
\end{code}
%</ulc>
%<*patterns>
\begin{code}
pattern `app f t  = `con (true , f , t , refl)
pattern `lam b    = `con (false , b , refl)
\end{code}
%</patterns>
%<*identity>
\begin{code}
id^U : TM UTLC tt
id^U = `lam (`var z)
\end{code}
%</identity>
