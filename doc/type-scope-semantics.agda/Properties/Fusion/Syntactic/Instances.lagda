\begin{code}
module Properties.Fusion.Syntactic.Instances where

open import Syntax.Calculus
open import Syntax.Type
open import Data.Var hiding (_<$>_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Environment
open import Semantics.Syntactic.Instances
open import Data.Relation as Rel hiding (_∙ᴿ_)
open import Properties.Fusion.Syntactic.Specification as Syntactic
open import Properties.Fusion.Specification as Fusion
open import Properties.Simulation.Instances using (VarTermᴿ)

open import Function
open import Relation.Binary.PropositionalEquality hiding (trans)
open ≡-Reasoning

open SynFusion


\end{code}
%<*renrenfus>
\begin{code}
RenRen : SynFusion  Syn^Ren Syn^Ren Syn^Ren
                    (λ ρᴬ ρᴮ → All Eqᴿ _ (select ρᴬ ρᴮ)) Eqᴿ
RenRen ._∙ᴿ_   = λ ρᴿ tᴿ → packᴿ λ { z → tᴿ ; (s v) → lookupᴿ ρᴿ v }
RenRen .th^𝓔ᴿ  = λ ρᴿ ρ → cong (λ v → th^Var v ρ) <$>ᴿ ρᴿ
RenRen .varᴿ   = λ ρᴿ v → cong `var (lookupᴿ ρᴿ v)
RenRen .zroᴿ   = refl
\end{code}
%</renrenfus>
\begin{code}
private
  variable
    σ : Type
    Γ Δ : List Type
    𝓣 : Type ─Scoped
    ρ₁ ρ₂ : (Γ ─Env) 𝓣 Δ
    t : Term σ Γ

\end{code}
%<*renren>
\begin{code}
renren : (t : Term σ Γ) → ren ρ₂ (ren ρ₁ t) ≡ ren (select ρ₁ ρ₂) t
renren =  let fus = Syntactic.Fundamental.lemma RenRen
          in Fusion.Fundamental.lemma fus reflᴿ
\end{code}
%</renren>
%<*rensubfus>
\begin{code}
RenSub : SynFusion  Syn^Ren Syn^Sub Syn^Sub
                    (λ ρᴬ ρᴮ → All Eqᴿ _ (select ρᴬ ρᴮ)) Eqᴿ
\end{code}
%</rensubfus>
\begin{code}
RenSub ._∙ᴿ_   = λ ρᴿ tᴿ → packᴿ λ { z → tᴿ ; (s v) → lookupᴿ ρᴿ v }
RenSub .th^𝓔ᴿ  = λ ρᴿ ρ → cong (λ t → th^Term t ρ) <$>ᴿ ρᴿ
RenSub .varᴿ   = λ ρᴿ v → lookupᴿ ρᴿ v
RenSub .zroᴿ   = refl

\end{code}
%<*rensub>
\begin{code}
rensub : (t : Term σ Γ) → sub ρ₂ (ren ρ₁ t) ≡ sub (select ρ₁ ρ₂) t
rensub =  let fus = Syntactic.Fundamental.lemma RenSub
          in Fusion.Fundamental.lemma fus reflᴿ
\end{code}
%</rensub>
%<*subrenfus>
\begin{code}
SubRen : SynFusion  Syn^Sub Syn^Ren Syn^Sub
                    (λ ρᴬ ρᴮ → All Eqᴿ _ (ren ρᴮ <$> ρᴬ)) VarTermᴿ
\end{code}
%</subrenfus>
\begin{code}
SubRen ._∙ᴿ_ {ρᴬ = ρᴬ} {ρᴮ = ρᴮ} {ρᴬᴮ = ρᴬᴮ} {tᴮ = tᴮ} {tᴬᴮ = tᴬᴮ} = λ ρᴿ tᴿ → packᴿ λ where
  z     → tᴿ
  (s v) → begin
    th^Term (th^Term (lookup ρᴬ v) extend) (ρᴮ ∙ tᴮ)
      ≡⟨ renren (lookup ρᴬ v) ⟩
    th^Term (lookup ρᴬ v) ρᴮ
      ≡⟨ lookupᴿ ρᴿ v ⟩
    lookup ρᴬᴮ v
      ∎
SubRen .th^𝓔ᴿ {ρᴬ = ρᴬ} {ρᴮ = ρᴮ} {ρᴬᴮ = ρᴬᴮ} = λ ρᴿ ρ → packᴿ λ v → begin
  th^Term (lookup ρᴬ v) (select ρᴮ ρ)
    ≡⟨ sym (renren (lookup ρᴬ v)) ⟩
  th^Term (th^Term (lookup ρᴬ v) ρᴮ) ρ
    ≡⟨ cong (λ t → th^Term t ρ) (lookupᴿ ρᴿ v) ⟩
  th^Term (lookup ρᴬᴮ v) ρ
    ∎
SubRen .varᴿ   = λ ρᴿ v → lookupᴿ ρᴿ v
SubRen .zroᴿ   = refl

\end{code}
%<*subren>
\begin{code}
subren : (t : Term σ Γ) → ren ρ₂ (sub ρ₁ t) ≡ sub (ren ρ₂ <$> ρ₁) t
subren =  let fus = Syntactic.Fundamental.lemma SubRen
          in Fusion.Fundamental.lemma fus reflᴿ
\end{code}
%</subren>
%<*subsubfus>
\begin{code}
SubSub : SynFusion  Syn^Sub Syn^Sub Syn^Sub
                    (λ ρᴬ ρᴮ → All Eqᴿ _ (sub ρᴮ <$> ρᴬ)) Eqᴿ
\end{code}
%</subsubfus>
\begin{code}
SubSub ._∙ᴿ_ {ρᴬ = ρᴬ} {ρᴮ = ρᴮ} {ρᴬᴮ = ρᴬᴮ} {tᴮ = tᴮ} {tᴬᴮ = tᴬᴮ} = λ ρᴿ tᴿ → packᴿ λ where
  z     → tᴿ
  (s v) → begin
    sub (ρᴮ ∙ tᴮ) (th^Term (lookup ρᴬ v) extend)
      ≡⟨ rensub (lookup ρᴬ v) ⟩
    sub ρᴮ (lookup ρᴬ v)
      ≡⟨ lookupᴿ ρᴿ v ⟩
    lookup ρᴬᴮ v
      ∎
SubSub .th^𝓔ᴿ {ρᴬ = ρᴬ} {ρᴮ = ρᴮ} {ρᴬᴮ = ρᴬᴮ} = λ ρᴿ ρ → packᴿ λ v → begin
  sub ((λ t → th^Term t ρ) <$> ρᴮ) (lookup ρᴬ v)
    ≡⟨ sym (subren (lookup ρᴬ v)) ⟩
  th^Term (sub ρᴮ (lookup ρᴬ v)) ρ
    ≡⟨ cong (λ t → th^Term t ρ) (lookupᴿ ρᴿ v) ⟩
  th^Term (lookup ρᴬᴮ v) ρ
    ∎
SubSub .varᴿ   = λ ρᴿ v → lookupᴿ ρᴿ v
SubSub .zroᴿ   = refl

\end{code}
%<*subsub>
\begin{code}
subsub : (t : Term σ Γ) → sub ρ₁ (sub ρ₂ t) ≡ sub (sub ρ₁ <$> ρ₂) t
subsub =  let fus = Syntactic.Fundamental.lemma SubSub
          in Fusion.Fundamental.lemma fus reflᴿ
\end{code}
%</subsub>
