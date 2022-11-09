\begin{code}
{-# OPTIONS --safe #-}

module Data.Environment where

open import Data.Nat.Base as ℕ
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Sum using (_⊎_)
open import Function
open import Category.Functor
open import Relation.Unary using (IUniversal; _⇒_)
open import Relation.Binary.PropositionalEquality as PEq hiding ([_])

open import Data.Var hiding (_<$>_)

private

  variable
    I A : Set
    i j k l σ : I
    S T U : List I → Set
    𝓥 𝓦 𝓒 : I ─Scoped
    Γ Δ Θ : List I
    F : Set → Set

infix 3 _─Env
\end{code}
%<*env>
\begin{code}
record _─Env (Γ : List I) (𝓥 : I ─Scoped) (Δ : List I) : Set where
  constructor pack
  field lookup : Var i Γ → 𝓥 i Δ
\end{code}
%</env>
\begin{code}

open _─Env public
\end{code}
%<*thinning>
\begin{code}
Thinning : List I → List I → Set
Thinning Γ Δ = (Γ ─Env) Var Δ
\end{code}
%</thinning>
%<*empty>
\begin{code}
ε : ([] ─Env) 𝓥 Δ
lookup ε ()
\end{code}
%</empty>
%<*envmap>
\begin{code}
_<$>_ : (∀ {i} → 𝓥 i Δ → 𝓦 i Θ) → (Γ ─Env) 𝓥 Δ → (Γ ─Env) 𝓦 Θ
lookup (f <$> ρ) k = f (lookup ρ k)
\end{code}
%</envmap>
\begin{code}

data Split (i : I) Γ Δ : Var i (Γ ++ Δ) → Set where
  inj₁ : (k : Var i Γ) → Split i Γ Δ (injectˡ Δ k)
  inj₂ : (k : Var i Δ) → Split i Γ Δ (injectʳ Γ k)

split : ∀ Γ (k : Var i (Γ ++ Δ)) → Split i Γ Δ k
split []      k     = inj₂ k
split (σ ∷ Γ) z     = inj₁ z
split (σ ∷ Γ) (s k) with split Γ k
... | inj₁ k₁ = inj₁ (s k₁)
... | inj₂ k₂ = inj₂ k₂

split-injectˡ : (Γ : List I) (v : Var σ Δ) → split Δ (injectˡ Γ v) ≡ inj₁ v
split-injectˡ Γ z                               = refl
split-injectˡ Γ (s v) rewrite split-injectˡ Γ v = refl

split-injectʳ : (Δ : List I) (v : Var σ Γ) → split Δ (injectʳ Δ v) ≡ inj₂ v
split-injectʳ []      v                           = refl
split-injectʳ (_ ∷ Δ) v rewrite split-injectʳ Δ v = refl

_++^Env_ : (Γ ─Env) 𝓥 Θ → (Δ ─Env) 𝓥 Θ → (Γ ++ Δ ─Env) 𝓥 Θ
lookup (_++^Env_ {Γ = Γ} ρ₁ ρ₂) k with split Γ k
... | inj₁ k₁ = lookup ρ₁ k₁
... | inj₂ k₂ = lookup ρ₂ k₂

injectˡ-++^Env : ∀ (ρ₁ : (Γ ─Env) 𝓥 Θ) (ρ₂ : (Δ ─Env) 𝓥 Θ) (v : Var i Γ) →
             lookup (ρ₁ ++^Env ρ₂) (injectˡ Δ v) ≡ lookup ρ₁ v
injectˡ-++^Env {Δ = Δ} ρ₁ ρ₂ v rewrite split-injectˡ Δ v = refl

injectʳ-++^Env : ∀ (ρ₁ : (Γ ─Env) 𝓥 Θ) (ρ₂ : (Δ ─Env) 𝓥 Θ) (v : Var i Δ) →
             lookup (ρ₁ ++^Env ρ₂) (injectʳ Γ v) ≡ lookup ρ₂ v
injectʳ-++^Env {Γ = Γ} ρ₁ ρ₂ v rewrite split-injectʳ Γ v = refl

infixl 10 _∙_
\end{code}
%<*extension>
\begin{code}
_∙_ : (Γ ─Env) 𝓥 Δ → 𝓥 σ Δ → ((σ ∷ Γ) ─Env) 𝓥 Δ
lookup (ρ ∙ v) z      = v
lookup (ρ ∙ v) (s k)  = lookup ρ k
\end{code}
%</extension>

%<*identity>
\begin{code}
identity : Thinning Γ Γ
lookup identity k = k
\end{code}
%</identity>

%<*select>
\begin{code}
select : Thinning Γ Δ → (Δ ─Env) 𝓥 Θ → (Γ ─Env) 𝓥 Θ
lookup (select ren ρ) k = lookup ρ (lookup ren k)
\end{code}
%</select>

%<*extend>
\begin{code}
extend : Thinning Γ (σ ∷ Γ)
lookup extend v = s v
\end{code}
%</extend>

\begin{code}
bind : ∀ σ → Thinning Γ (σ ∷ Γ)
bind _ = extend

-- Like the flipped version of _++^Env_ but it computes. Which is convenient when
-- dealing with concrete Γs (cf. βred)
_<+>_ : (Δ ─Env) 𝓥 Θ → (Γ ─Env) 𝓥 Θ → (Γ ++ Δ ─Env) 𝓥 Θ
_<+>_ {Γ = []}    ρ₁ ρ₂ = ρ₁
_<+>_ {Γ = _ ∷ Γ} ρ₁ ρ₂ = (ρ₁ <+> select extend ρ₂) ∙ lookup ρ₂ z

injectˡ-<+> : ∀ Δ (ρ₁ : (Δ ─Env) 𝓥 Θ) (ρ₂ : (Γ ─Env) 𝓥 Θ) (v : Var i Γ) →
              lookup (ρ₁ <+> ρ₂) (injectˡ Δ v) ≡ lookup ρ₂ v
injectˡ-<+> Δ ρ₁ ρ₂ z     = refl
injectˡ-<+> Δ ρ₁ ρ₂ (s v) = injectˡ-<+> Δ ρ₁ (select extend ρ₂) v

injectʳ-<+> : ∀ Γ (ρ₁ : (Δ ─Env) 𝓥 Θ) (ρ₂ : (Γ ─Env) 𝓥 Θ) (v : Var i Δ) →
              lookup (ρ₁ <+> ρ₂) (injectʳ Γ v) ≡ lookup ρ₁ v
injectʳ-<+> []      ρ₁ ρ₂ v = refl
injectʳ-<+> (x ∷ Γ) ρ₁ ρ₂ v = injectʳ-<+> Γ ρ₁ (select extend ρ₂) v


\end{code}
%<*box>
\begin{code}
□ : (List I → Set) → (List I → Set)
(□ T) Γ = ∀[ Thinning Γ ⇒ T ]
\end{code}
%</box>

%<*mapbox>
\begin{code}
map^□ : ∀[ S ⇒ T ] → ∀[ □ S ⇒ □ T ]
map^□ f v th = f (v th)
\end{code}
%</mapbox>

\begin{code}
-- functor laws
map^□-identity : ∀ (v : □ S i) →
  (λ {j} (th : Thinning i j) →
  map^□ (λ x → x) v th) ≡ v
map^□-identity v = refl

map^□-compose :
  ∀ (f : ∀[ S ⇒ T ]) (g : ∀[ T ⇒ U ]) (v : □ S i) →
  (λ {j : List I} (th : Thinning i j) →
  map^□ g (map^□ f v) th) ≡ map^□ (g ∘ f) v
map^□-compose f g v = refl
\end{code}

\begin{code}
infixl 5 _◃_
record ◇ (T : List I → Set) (Γ : List I) : Set where
  constructor _◃_
  field {support} : List I
        value     : T support
        thinning  : Thinning support Γ
\end{code}
%<*extract>
\begin{code}
extract : ∀[ □ T ⇒ T ]
extract t = t identity
\end{code}
%</extract>
%<*duplicate>
\begin{code}
duplicate  : ∀[ □ T ⇒ □ (□ T)  ]
duplicate t ρ σ = t (select ρ σ)
\end{code}
%</duplicate>
\begin{code}

-- comonad laws
extract-duplicate₁ : ∀ (v : □ T i) →
  (λ {j} (th : Thinning i j) → extract (duplicate v) th) ≡ v
extract-duplicate₁ v = refl

extract-duplicate₂ : ∀ (v : □ T i) →
  (λ {j} (th : Thinning i j) → map^□ extract (duplicate v) th) ≡ v
extract-duplicate₂ v = refl

duplicate-duplicate : ∀ (v : □ T i) →
  (λ {j} (thᵢⱼ : Thinning i j)
     {k} (thⱼₖ : Thinning j k)
     {l} (thₖₗ : Thinning k l) →
  duplicate (duplicate v) thᵢⱼ thⱼₖ thₖₗ)
  ≡ map^□ duplicate (duplicate v)
duplicate-duplicate v = refl


module □ where

  join : ∀[ □ (□ T) ⇒ □ T ]
  join = extract

\end{code}
%<*thinnable>
\begin{code}
Thinnable : (List I → Set) → Set
Thinnable T = ∀[ T ⇒ □ T ]
\end{code}
%</thinnable>
%<*thVar>
\begin{code}
th^Var : Thinnable (Var i)
th^Var v ρ = lookup ρ v
\end{code}
%</thVar>
%<*thEnv>
\begin{code}
th^Env : (∀ {i} → Thinnable (𝓥 i)) → Thinnable ((Γ ─Env) 𝓥)
lookup (th^Env th^𝓥 ρ ren) k = th^𝓥 (lookup ρ k) ren
\end{code}
%</thEnv>
%<*thBox>
\begin{code}
th^□ : Thinnable (□ T)
th^□ = duplicate
\end{code}
%</thBox>
\begin{code}
curry : ∀[ ◇ S ⇒ T ] → ∀[ S ⇒ □ T ]
curry f v th = f (v ◃ th)

uncurry : ∀[ S ⇒ □ T ] → ∀[ ◇ S ⇒ T ]
uncurry f (v ◃ th) = f v th

module DI where

  th^◇ : Thinnable (◇ T)
  th^◇ (t ◃ Θ⊆Γ) Γ⊆Δ = t ◃ select Θ⊆Γ Γ⊆Δ

  pure : ∀[ T ⇒ ◇ T ]
  pure t = t ◃ identity

  join : ∀[ ◇ (◇ T) ⇒ ◇ T ]
  join (t ◃ Γ⊆Δ ◃ Δ⊆Θ) = t ◃ select Γ⊆Δ Δ⊆Θ

  map : ∀[ S ⇒ T ] → ∀[ ◇ S ⇒ ◇ T ]
  map f (sΓ ◃ Γ⊆Δ) = f sΓ ◃ Γ⊆Δ

  _>>=_ : ◇ S Γ → ∀[ S ⇒ ◇ T ] → ◇ T Γ
  ◇s >>= f = join (map f ◇s)

  run : Thinnable T → ∀[ ◇ T ⇒ T ]
  run = uncurry
\end{code}
%<*thConst>
\begin{code}
th^const : Thinnable {I} (const A)
th^const a _ = a
\end{code}
%</thConst>
\begin{code}
th^Functor : RawFunctor F → Thinnable T → Thinnable (F ∘ T)
th^Functor F th^T ft ρ = (λ t → th^T t ρ) F.<$> ft
  where module F = RawFunctor F
\end{code}
%<*kripke>
\begin{code}
Kripke : (𝓥 𝓒 : I ─Scoped) → (List I → I ─Scoped)
Kripke 𝓥 𝓒 []  j = 𝓒 j
Kripke 𝓥 𝓒 Δ   j = □ ((Δ ─Env) 𝓥 ⇒ 𝓒 j)
\end{code}
%</kripke>
\begin{code}

_$$_ : ∀[ Kripke 𝓥 𝓒 Γ i ⇒ (Γ ─Env) 𝓥 ⇒ 𝓒 i ]
_$$_ {Γ = []}    f ts = f
_$$_ {Γ = _ ∷ _} f ts = extract f ts

th^Kr : (Γ : List I) → (∀ {i} → Thinnable (𝓒 i)) →
        Thinnable (Kripke 𝓥 𝓒 Γ i)
th^Kr []       th^𝓒 = th^𝓒
th^Kr (_ ∷ _)  th^𝓒 = th^□

open import Category.Applicative

module _ {A : Set → Set} {{app : RawApplicative A}} where

 private module A = RawApplicative app
 open A

 sequenceA : (Γ ─Env) (λ i Γ → A (𝓥 i Γ)) Δ → A ((Γ ─Env) 𝓥 Δ)
 sequenceA = go _ where

   go : ∀ Γ → (Γ ─Env) (λ i Γ → A (𝓥 i Γ)) Δ → A ((Γ ─Env) 𝓥 Δ)
   go []       ρ = pure ε
   go (σ ∷ Γ)  ρ = _∙_ A.<$> go Γ (select extend ρ) ⊛ lookup ρ z
\end{code}
