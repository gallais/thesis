\begin{code}
module Generic.Data where

open import Relation.Unary
open import Size
open import Data.Empty
open import Data.Bool
open import Data.Nat using (ℕ ; suc)
open import Data.Unit
open import Data.Product as Prod
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

private
  variable
   A B : Set

\end{code}
%<*desc>
\begin{code}
data Desc (I J : Set) : Set₁ where
  `σ : (A : Set) → (A → Desc I J) → Desc I J
  `X : J → Desc I J → Desc I J
  `∎ : I → Desc I J
\end{code}
%</desc>
\begin{code}

module _ {I J : Set} where
 private
   variable
     X Y : J → Set

 infixr 5 _`+_

 `K : Set → I → Desc I J
 `K A i = `σ A (λ _ → `∎ i)

 _`+_ : Desc I J → Desc I J → Desc I J
 d `+ e = `σ Bool $ λ { true  → d ; false → e }
\end{code}
%<*interp>
\begin{code}
 ⟦_⟧ : Desc I J → (J → Set) → (I → Set)
 ⟦ `σ A d  ⟧ X i = Σ[ a ∈ A ] (⟦ d a ⟧ X i)
 ⟦ `X j d  ⟧ X i = X j × ⟦ d ⟧ X i
 ⟦ `∎ j    ⟧ X i = i ≡ j
\end{code}
%</interp>
%<*fmap>
\begin{code}
 fmap : (d : Desc I J) → ∀[ X ⇒ Y ] → ∀[ ⟦ d ⟧ X ⇒ ⟦ d ⟧ Y ]
 fmap (`σ A d)  f (a , v)  = (a , fmap (d a) f v)
 fmap (`X j d)  f (r , v)  = (f r , fmap d f v)
 fmap (`∎ i)    f t        = t
\end{code}
%</fmap>
\begin{code}
private
  variable
    I : Set
    i : I
    s : Size
    X : I → Set

module _ {I : Set} where
\end{code}
%<*mu>
\begin{code}
 data μ (d : Desc I I) (s : Size) : I → Set where
   `con : {s' : Size< s} → ⟦ d ⟧ (μ d s') i → μ d s i
\end{code}
%</mu>
%<*fold>
\begin{code}
fold : (d : Desc I I) → ∀[ ⟦ d ⟧ X ⇒ X ] → ∀[ μ d s ⇒ X ]
fold d alg (`con t) = alg (fmap d (fold d alg) t)
\end{code}
%</fold>
\begin{code}
finD : Desc ℕ ℕ
finD =  `σ ℕ $ λ index →
        `σ Bool $ λ isZero → if isZero
        then `∎ (suc index)
        else `X index (`∎ (suc index))

fin : ℕ → Set
fin = μ finD ∞

fin0-elim : fin 0 → ⊥
fin0-elim (`con (_ , true , ()))
fin0-elim (`con (_ , false , _ , ()))

fz : ∀ n → fin (suc n)
fz n = `con (n , true , refl)

fs : ∀ n → fin n → fin (suc n)
fs n k = `con (n , false , k , refl)

\end{code}
%<*listD>
\begin{code}
listD : Set → Desc ⊤ ⊤
listD A =  `σ Bool $ λ isNil →
           if isNil then `∎ tt
           else `σ A (λ _ → `X tt (`∎ tt))
\end{code}
%</listD>

%<*list>
\begin{code}
List : Set → Set
List A = μ (listD A) ∞ tt
\end{code}
%</list>

\begin{code}
infixr 10 _∷_
\end{code}
%<*nil>
\begin{code}
pattern []'  = (true , refl)
pattern []   = `con []'
\end{code}
%</nil>
%<*cons>
\begin{code}
pattern _∷'_ x xs  = (false , x , xs , refl)
pattern _∷_ x xs   = `con (x ∷' xs)
\end{code}
%</cons>

\begin{code}
example : List (List Bool)
example  = (false ∷ []) ∷ (true ∷ []) ∷ []
\end{code}
%<*vecD>
\begin{code}
vecD : Set → Desc ℕ ℕ
vecD A =  `σ Bool $ λ isNil →
          if isNil then `∎ 0
          else `σ ℕ (λ n → `σ A (λ _ → `X n (`∎ (suc n))))
\end{code}
%</vecD>
\begin{code}
Vec : Set → ℕ → Set
Vec A = μ (vecD A) ∞

\end{code}
%<*foldr>
\begin{code}
foldr : (A → B → B) → B → List A → B
foldr c n = fold (listD _) $ λ where
  []'          → n
  (hd ∷' rec)  → c hd rec
\end{code}
%</foldr>
\begin{code}
_++_ : {A : Set} → List A  → List A → List A
_++_ = foldr (λ hd rec → hd ∷_ ∘ rec) id

flatten : {A : Set} → List (List A) → List A
flatten = foldr _++_ []

test : flatten example ≡ false ∷ true ∷ []
test = refl
