\begin{code}
module Generic.Semantics.Syntactic where

open import Size
open import Data.List hiding ([_] ; lookup)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Relation.Unary
open import Data.Var
open import Data.Var.Varlike
open import Data.Environment
open import Data.Relation
open import Generic.Syntax
open import Generic.Semantics

open Semantics

module _ {I : Set} {d : Desc I} where
 private
    variable
      σ : I
      Γ Δ : List I

\end{code}
%<*renaming>
\begin{code}
 Renaming : Semantics d Var (Tm d ∞)
 Renaming  .th^𝓥  = λ k ρ → lookup ρ k
 Renaming  .var   = `var
 Renaming  .alg   = `con ∘ fmap d (reify vl^Var)
\end{code}
%</renaming>
%<*thTm>
\begin{code}
 th^Tm : Thinnable (Tm d ∞ σ)
 th^Tm t ρ = Semantics.semantics Renaming ρ t
\end{code}
%</thTm>
\begin{code}
 ren : Thinning Γ Δ → (Γ ─Comp) (Tm d ∞) Δ
 ren = Semantics.semantics Renaming

 vl^Tm : VarLike (Tm d ∞)
 new   vl^Tm = `var z
 th^𝓥  vl^Tm = th^Tm
\end{code}
%<*substitution>
\begin{code}
 Substitution : Semantics d (Tm d ∞) (Tm d ∞)
 Substitution .th^𝓥  = th^Tm
 Substitution .var   = id
 Substitution .alg   = `con ∘ fmap d (reify vl^Tm)
\end{code}
%</substitution>
\begin{code}
 module PAPERONLY where
\end{code}
%<*sub>
\begin{code}
  sub :  (Γ ─Env) (Tm d ∞) Δ → Tm d ∞ σ Γ → Tm d ∞ σ Δ
  sub ρ t = Semantics.semantics Substitution ρ t
\end{code}
%</sub>
\begin{code}
 sub : ∀ {s} → (Γ ─Env) (Tm d ∞) Δ → Tm d s σ Γ → Tm d ∞ σ Δ
 sub ρ t = Semantics.semantics Substitution ρ t

 vl^VarTm : VarLikeᴿ VarTmᴿ vl^Var vl^Tm
 VarLikeᴿ.newᴿ  vl^VarTm = refl
 VarLikeᴿ.thᴿ   vl^VarTm = λ σ → cong (ren σ)

 reify^Tm : ∀ Δ {σ} → ∀[ Kripke (Tm d ∞) (Tm d ∞) Δ σ ⇒ (Δ ++_) ⊢ Tm d ∞ σ ]
 reify^Tm Δ = reify vl^Tm Δ _

 lookup-base^Tm : {Γ : List I} {σ : I} (k : Var σ Γ) → lookup (base vl^Tm) k ≡ `var k
 lookup-base^Tm z                              = refl
 lookup-base^Tm (s k) rewrite lookup-base^Tm k = refl

 base^VarTmᴿ : ∀ {Γ} → All VarTmᴿ Γ (base vl^Var) (base vl^Tm)
 lookupᴿ base^VarTmᴿ k = begin
   `var (lookup (base vl^Var) k) ≡⟨ cong `var (lookup-base^Var k) ⟩
   `var k                        ≡⟨ sym (lookup-base^Tm k) ⟩
   lookup (base vl^Tm) k ∎

 infix 5 _[_
 infix 6 _/0]

 _/0] : ∀ {σ Γ} → Tm d ∞ σ Γ → (σ ∷ Γ ─Env) (Tm d ∞) Γ
 _/0] = singleton vl^Tm

 _[_ : ∀ {σ τ Γ} → Tm d ∞ τ (σ ∷ Γ) → (σ ∷ Γ ─Env) (Tm d ∞) Γ → Tm d ∞ τ Γ
 t [ ρ = sub ρ t

\end{code}
