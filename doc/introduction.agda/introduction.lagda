\begin{code}
module introduction where

open import Agda.Builtin.Equality

\end{code}
%<*idType>
\begin{code}
ID : Set₁
ID = {A : Set} → A → A
\end{code}
%</idType>

%<*idTerm>
\begin{code}
id : ID
id x = x
\end{code}
%</idTerm>

%<*bottom>
\begin{code}
data ⊥ : Set where
\end{code}
%</bottom>

%<*bottomelim>
\begin{code}
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()
\end{code}
%</bottomelim>

%<*bool>
\begin{code}
data Bool : Set where
  true   : Bool
  false  : Bool
\end{code}
%</bool>

%<*boolis2>
\begin{code}
true≢false : true ≡ false → ⊥
true≢false ()
\end{code}
%</boolis2>

%<*ifte>
\begin{code}
if_then_else_ : {A : Set} → Bool → A → A → A
if true   then t else f = t
if false  then t else f = f
\end{code}
%</ifte>

%<*not>
\begin{code}
not : Bool → Bool
not b = if b then false else true
\end{code}
%</not>



%<*variable>
\begin{code}
variable
  A B C : Set
\end{code}
%</variable>



%<*nat>
\begin{code}
data ℕ : Set where
  zero  : ℕ
  suc   : ℕ → ℕ
\end{code}
%</nat>


%<*add>
\begin{code}
_+_ : ℕ → ℕ → ℕ
zero   + n = n
suc m  + n = suc (m + n)
\end{code}
%</add>




%<*unit>
\begin{code}
record ⊤ : Set where
  constructor tt
\end{code}
%</unit>

%<*uniteq>
\begin{code}
_ : (t u : ⊤) → t ≡ u
_ = λ t u → refl
\end{code}
%</uniteq>




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
\end{code}


%<*paireq>
\begin{code}
_ : (p : A × B) → p ≡ (fst p , snd p)
_ = λ p → refl
\end{code}
%</paireq>

%<*duplicate>
\begin{code}
duplicate : A → A × A
duplicate a = (a , a)
\end{code}
%</duplicate>

\begin{code}
module recsyntax where
\end{code}
%<*swaprecord>
\begin{code}
 swap : A × B → B × A
 swap (a , b) = record
   { fst  = b
   ; snd  = a
   }
\end{code}
%</swaprecord>

\begin{code}
module recpattern where
\end{code}
%<*swaprecordlhs>
\begin{code}
 swap : A × B → B × A
 swap record  { fst  = a
              ; snd  = b
              } = (b , a)
\end{code}
%</swaprecordlhs>

\begin{code}
module prefix where
\end{code}
%<*swapprefix>
\begin{code}
 swap : A × B → B × A
 swap p = (snd p , fst p)
\end{code}
%</swapprefix>

\begin{code}
module suffix where
\end{code}
%<*swapsuffix>
\begin{code}
 swap : A × B → B × A
 swap p = (p .snd , p .fst)
\end{code}
%</swapsuffix>

\begin{code}
module coprefix where
\end{code}
%<*swapcoprefix>
\begin{code}
 swap : A × B → B × A
 fst  (swap (a , b)) = b
 snd  (swap (a , b)) = a
\end{code}
%</swapcoprefix>

\begin{code}
module cosuffix where
\end{code}
%<*swapcosuffix>
\begin{code}
 swap : A × B → B × A
 swap (a , b) .fst  = b
 swap (a , b) .snd  = a
\end{code}
%</swapcosuffix>

\begin{code}
module coanonymous where
\end{code}
%<*swapcoanonymous>
\begin{code}
 swap : A × B → B × A
 swap (a , b) = λ where
   .fst  → b
   .snd  → a
\end{code}
%</swapcoanonymous>

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
%<*cong>
\begin{code}
cong : ∀ (f : A → B) {a₁ a₂} → a₁ ≡ a₂ → f a₁ ≡ f a₂
cong f refl = refl
\end{code}
%</cong>
%<*cong2>
\begin{code}
cong₂ : ∀ (f : A → B → C) {a₁ a₂ b₁ b₂} →
        a₁ ≡ a₂ → b₁ ≡ b₂ → f a₁ b₁ ≡ f a₂ b₂
cong₂ f refl refl = refl
\end{code}
%</cong2>
%<*mapntuple>
\begin{code}
map^-Tuple : ∀ n → (A → B) → n -Tuple A → n -Tuple B
map^-Tuple zero     f tt        = tt
map^-Tuple (suc n)  f (a , as)  = f a , map^-Tuple n f as
\end{code}
%</mapntuple>
%<*mapidentity>
\begin{code}
map-identity :
  ∀ n {f : A → A} → (∀ a → f a ≡ a) →
  ∀ as → map^-Tuple n f as ≡ as
map-identity zero     f-id tt        = refl
map-identity (suc n)  f-id (a , as)  = cong₂ _,_ (f-id a) (map-identity n f-id as)
\end{code}
%</mapidentity>

%<*mapfusion>
\begin{code}
map-fusion :
  ∀ n {f : A → B} {g : B → C} {h} → (∀ a → g (f a) ≡ h a) →
  ∀ as → map^-Tuple n g (map^-Tuple n f as) ≡ map^-Tuple n h as
map-fusion zero     gf≈h tt        = refl
map-fusion (suc n)  gf≈h (a , as)  = cong₂ _,_ (gf≈h a) (map-fusion n gf≈h as)
\end{code}
%</mapfusion>

%<*mapreplicate>
\begin{code}
map-replicate : ∀ n (f : A → B) (a : A) →
  map^-Tuple n f (replicate n a) ≡ replicate n (f a)
map-replicate zero     f a = refl
map-replicate (suc n)  f a = cong (f a ,_) (map-replicate n f a)
\end{code}
%</mapreplicate>

%<*sigma>
\begin{code}
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field  proj₁ : A
         proj₂ : B proj₁
\end{code}
%</sigma>

%<*tuple>
\begin{code}
record Tuple (A : Set) : Set where
  constructor mkTuple
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
    map^Rose f (leaf a)               = leaf (f a)
    map^Rose f (node (mkTuple n rs))  = node (mkTuple n (map^Roses n f rs))

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
