\begin{code}
module introduction where

\end{code}

%<*variable>
\begin{code}
variable
  A B : Set
\end{code}
%</variable>

%<*nat>
\begin{code}
data ℕ : Set where
  zero  : ℕ
  suc   : ℕ → ℕ
\end{code}
%</nat>
%<*unit>
\begin{code}
record ⊤ : Set where
  constructor tt
\end{code}
%</unit>
\begin{code}
infixr 5 _×_
infixr 20 _,_
\end{code}
%<*pair>
\begin{code}
record _×_ (A B : Set) : Set where
  constructor _,_
  field fst : A; snd : B
\end{code}
%</pair>
\begin{code}
open _×_
infixl 5 _-Tuple_
\end{code}
%<*ntuple>
\begin{code}
_-Tuple_ : ℕ → Set → Set
zero   -Tuple A = ⊤
suc n  -Tuple A = A × (n -Tuple A)
\end{code}
%</ntuple>
%<*replicate>
\begin{code}
replicate : ∀ n → A → n -Tuple A
replicate zero     a = tt
replicate (suc n)  a = a , replicate n a
\end{code}
%</replicate>
%<*mapntuple>
\begin{code}
map^-Tuple : ∀ n → (A → B) → n -Tuple A → n -Tuple B
map^-Tuple zero     f tt        = tt
map^-Tuple (suc n)  f (a , as)  = f a , map^-Tuple n f as
\end{code}
%</mapntuple>
\begin{code}
infixl 19 _<|_
\end{code}
%<*tuple>
\begin{code}
record Tuple (A : Set) : Set where
  constructor _<|_
  field length   : ℕ
        content  : length -Tuple A
\end{code}
%</tuple>
\begin{code}
open Tuple
\end{code}
%<*maptuple>
\begin{code}
map^Tuple : (A → B) → Tuple A → Tuple B
map^Tuple f as = λ where
  .length   → as .length
  .content  → map^-Tuple (as .length) f (as .content)
\end{code}
%</maptuple>
\begin{code}
open import Size

module Unsized where

\end{code}
%<*rose>
\begin{code}
  data Rose (A : Set) : Set where
    leaf  : A → Rose A
    node  : Tuple (Rose A) → Rose A
\end{code}
%</rose>
%<*maprose>
\begin{code}
  {-# TERMINATING #-}
  map^Rose : (A → B) → Rose A → Rose B
  map^Rose f (leaf a)   = leaf (f a)
  map^Rose f (node rs)  = node (map^Tuple (map^Rose f) rs)
\end{code}
%</maprose>
\begin{code}

module Inlined where

  open Unsized using (Rose); open Rose

\end{code}
%<*inlinedmaprose>
\begin{code}
  mutual

    map^Rose : (A → B) → Rose A → Rose B
    map^Rose f (leaf a)   = leaf (f a)
    map^Rose f (node rs)  = node (_ <| map^Roses (rs .length) f (rs .content))

    map^Roses : ∀ n → (A → B) → n -Tuple (Rose A) → n -Tuple (Rose B)
    map^Roses zero     f rs        = tt
    map^Roses (suc n)  f (r , rs)  = map^Rose f r , map^Roses n f rs
\end{code}
%</inlinedmaprose>
\begin{code}
module Implicit where

\end{code}
%<*irose>
\begin{code}
  data Rose (A : Set) (i : Size) : Set where
    leaf  : A → Rose A i
    node  : {j : Size< i} → Tuple (Rose A j) → Rose A i
\end{code}
%</irose>
%<*mapirose>
\begin{code}
  map^Rose : ∀ {i} → (A → B) → Rose A i → Rose B i
  map^Rose f (leaf a)   = leaf (f a)
  map^Rose f (node rs)  = node (map^Tuple (map^Rose f) rs)
\end{code}
%</mapirose>
\begin{code}
module Explicit where
\end{code}
%<*erose>
\begin{code}
  data Rose (A : Set) (i : Size) : Set where
    leaf  : A → Rose A i
    node  : (j : Size< i) → Tuple (Rose A j) → Rose A i
\end{code}
%</erose>
%<*maperose>
\begin{code}
  map^Rose : ∀ i → (A → B) → Rose A i → Rose B i
  map^Rose i f (leaf a)     = leaf (f a)
  map^Rose i f (node j rs)  = node j (map^Tuple (map^Rose j f) rs)
\end{code}
%</maperose>
\begin{code}

\end{code}
