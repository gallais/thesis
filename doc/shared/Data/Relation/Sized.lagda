\begin{code}

{-# OPTIONS --sized-types #-}

module Data.Relation.Sized where

open import Size
open import Data.Relation
open import Data.Var
open import Generic.Syntax
open import Agda.Builtin.Equality

private
  variable
    I : Set

module _ {d : Desc I} where

 VarTmᴿ : Rel Var (Tm d ∞)
 rel VarTmᴿ i v t = `var v ≡ t

\end{code}
