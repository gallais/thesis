\begin{code}
module Stdlib where

private

  variable
    A B : Set
\end{code}

%<*implication>
\begin{code}
_⇒_ : (A → Set) → (A → Set) → (A → Set)
(P ⇒ Q) x = P x → Q x
\end{code}
%</implication>

%<*forall>
\begin{code}
∀[_] : (A → Set) → Set
∀[_] P = ∀ {x} → P x
\end{code}
%</forall>

%<*sigma>
\begin{code}
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field  proj₁ : A
         proj₂ : B proj₁
\end{code}
%</sigma>

%<*exists>
\begin{code}
∃⟨_⟩ : (A → Set) → Set
∃⟨_⟩ P = Σ _ P
\end{code}
%</exists>

%<*update>
\begin{code}
_⊢_ : (A → B) → (B → Set) → (A → Set)
(f ⊢ P) x = P (f x)
\end{code}
%</update>
