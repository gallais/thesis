\begin{code}
module Generic.Examples.Elaboration where

import Level
open import Size
open import Function
import Category.Monad as CM
open import Data.Bool
open import Data.Product as Prod
open import Data.List hiding ([_] ; lookup)
open import Data.List.Relation.Unary.All as All hiding (lookup)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
import Data.Maybe.Categorical as MC

open import Generic.Examples.TypeChecking
  using (Mode; LangC; Lang; Type; module M)
  ; open Mode; open LangC; open Type; open M

open import Generic.Examples.STLC

open import Relation.Unary hiding (_∈_)
open import Data.Var hiding (_<$>_)
open import Data.Environment hiding (_<$>_)
open import Generic.Syntax
open import Generic.Semantics

open import Relation.Binary.PropositionalEquality hiding ([_])

\end{code}
%<*typing>
\begin{code}
Typing : List Mode → Set
Typing = All (const Type)
\end{code}
%</typing>
\begin{code}

private
  variable
    σ : Type
    m : Mode
    ms ns : List Mode
\end{code}
%<*fromtyping>
\begin{code}
fromTyping : Typing ms → List Type
fromTyping []       = []
fromTyping (σ ∷ Γ)  = σ ∷ fromTyping Γ
\end{code}
%</fromtyping>
%<*elab>
\begin{code}
Elab : Type ─Scoped → Type → (ms : List Mode) → Typing ms → Set
Elab T σ _ Γ = T σ (fromTyping Γ)
\end{code}
%</elab>
%<*typemode>
\begin{code}
Type- : Mode ─Scoped
Type- Check  ms = ∀ Γ → (σ : Type) → Maybe (Elab (Tm STLC ∞) σ ms Γ)
Type- Infer  ms = ∀ Γ → Maybe (Σ[ σ ∈ Type ] Elab (Tm STLC ∞) σ ms Γ)
\end{code}
%</typemode>
%<*varmode>
\begin{code}
data Var- : Mode ─Scoped where
  `var : (infer : ∀ Γ → Σ[ σ ∈ Type ] Elab Var σ ms Γ) → Var- Infer ms
\end{code}
%</varmode>
\begin{code}
open import Data.List.Relation.Unary.Any hiding (lookup)
open import Data.List.Membership.Propositional

toVar : m ∈ ms → Var m ms
toVar (here refl) = z
toVar (there v) = s (toVar v)

fromVar : Var m ms → m ∈ ms
fromVar z = here refl
fromVar (s v) = there (fromVar v)

coth^Typing : Typing ns → Thinning ms ns → Typing ms
coth^Typing Δ ρ = All.tabulate (λ x∈Γ → All.lookup Δ (fromVar (lookup ρ (toVar x∈Γ))))

lookup-fromVar : ∀ Δ (v : Var m ms) → Var (All.lookup Δ (fromVar v)) (fromTyping Δ)
lookup-fromVar (_ ∷ _) z     = z
lookup-fromVar (_ ∷ _) (s v) = s (lookup-fromVar _ v)

erase^coth : ∀ ms Δ (ρ : Thinning ms ns) →
             Var σ (fromTyping (coth^Typing Δ ρ)) → Var σ (fromTyping Δ)
erase^coth []       Δ ρ ()
erase^coth (m ∷ ms) Δ ρ z     = lookup-fromVar Δ (lookup ρ z)
erase^coth (m ∷ ms) Δ ρ (s v) = erase^coth ms Δ (select extend ρ) v

th^Var- : Thinnable (Var- m)
th^Var- (`var infer) ρ = `var λ Δ →
  let (σ , v) = infer (coth^Typing Δ ρ) in
  σ , erase^coth _ Δ ρ v

open Semantics
\end{code}
%<*equal>
\begin{code}
_==_ : (σ τ : Type) → Maybe (σ ≡ τ)
α ==  α  = just refl
(σ₁ `→ τ₁) == (σ₂ `→ τ₂)  = do
  refl ← σ₁ == σ₂
  refl ← τ₁ == τ₂
  return refl
_ == _ = nothing
\end{code}
%</equal>
%<*arrow>
\begin{code}
data Arrow : Type → Set where
  _`→_ : (σ τ : Type) → Arrow (σ `→ τ)

isArrow : ∀ σ → Maybe (Arrow σ)
isArrow α         = nothing
isArrow (σ `→ τ)  = just (σ `→ τ)
\end{code}
%</arrow>
%<*app>
\begin{code}
APP : ∀[ Type- Infer ⇒ Type- Check ⇒ Type- Infer ]
APP f t Γ = do
  (σ`→τ , F)  ← f Γ
  (σ `→ τ)    ← isArrow σ`→τ
  T           ← t Γ σ
  return (τ , `app F T)
\end{code}
%</app>
%<*lam>
\begin{code}
VAR0 : Var- Infer (Infer ∷ ms)
VAR0 = `var λ where (σ ∷ _) → (σ , z)

LAM : ∀[ Kripke Var- Type- (Infer ∷ []) Check ⇒ Type- Check ]
LAM b Γ σ`→τ = do
  (σ `→ τ) ← isArrow σ`→τ
  B        ← b (bind Infer) (ε ∙ VAR0) (σ ∷ Γ) τ
  return (`lam B)
\end{code}
%</lam>
%<*emb>
\begin{code}
EMB : ∀[ Type- Infer ⇒ Type- Check ]
EMB t Γ σ = do
  (τ , T)  ← t Γ
  refl     ← σ == τ
  return T
\end{code}
%</emb>
%<*elaborate>
\begin{code}
Elaborate : Semantics Lang Var- Type-
Elaborate .th^𝓥  = th^Var-
Elaborate .var   = λ where (`var infer) Γ → just (map₂ `var (infer Γ))
Elaborate .alg   = λ where
  (App , f , t , refl)  → APP f t
  (Lam , b , refl)      → LAM b
  (Emb , t , refl)      → EMB t
  (Cut σ , t , refl)    → λ Γ → (σ ,_) <$> t Γ σ
\end{code}
%</elaborate>
\end{code}
