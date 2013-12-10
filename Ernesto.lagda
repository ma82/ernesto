# A universe of functors closed under μ and ν and monadic composition via copatterns and sized types

\begin{code}
{-# OPTIONS --copatterns --sized-types #-}
module Ernesto {lI} where
\end{code}

\begin{code}
open import Mod.Base hiding (■)
\end{code}

## Syntax

\begin{code}
infix 4 _`>>=_

data De (I : Set lI) : Set (S lI) where

  `1     :                                 De I
  _`×_   : (L R : De I)                  → De I

  `I     : (i : I)                       → De I
  `Σ `Π  : (S : Set lI)(T : S → De I)    → De I
  `μ `ν  : ∀ {R}(F : R → De (I ⊎ R)) → R → De I
  _`>>=_ : ∀ {J}(D : De J)(F : J → De I) → De I

infix 0 _▻_
_▻_ = λ (I O : Set lI) → O → De I
\end{code}

\begin{code}
`return : {I : ★ lI} → I → De I
`return = `I

map : {I J : ★ lI} → (I → J) → De I → De J
map f D = D `>>= `return ∘ f

_`∘_ : {A B C : ★ lI} → B ▻ C → A ▻ B → A ▻ C
(F `∘ G) a = F a `>>= G

`_[_] : {I J K : ★ lI} → (I ⊎ K ▻ J) → (I ▻ K) → I ▻ J
` F [ G ] = F `∘ ⊎.[ `I , G ]

% : {I J : ★ lI} → (I ⊎ J ▻ J) → I ▻ J
% F = ` F [ `ν F ]
\end{code}

## Semantics

\begin{code}
module Unsized where

  mutual

    ⟦_⟧ : ∀ {I} → De I → ∀ {lX} → Pow I lX → Set (lI ⊔ lX)

    ⟦ `1       ⟧ X = ⊤
    ⟦ L `× R   ⟧ X = ⟦ L ⟧ X × ⟦ R ⟧ X

    ⟦ `I k     ⟧ X = ^ lI (X k)
    ⟦ `Σ S T   ⟧ X = Σ S λ s → ⟦ T s ⟧ X
    ⟦ `Π S T   ⟧ X = Π S λ s → ⟦ T s ⟧ X
    ⟦ `μ F r   ⟧ X = μ F X r
    ⟦ `ν F r   ⟧ X = ν F X r
    ⟦ D `>>= F ⟧ X = ⟦ D ⟧ λ j → ⟦ F j ⟧ X

    data μ {I R}(F : (I ⊎ R) ▻ R){lX}(X : Pow I lX)(r : R) : Set (lI ⊔ lX) where
      [_] : ⟦ % F r ⟧ X → μ F X r

    record ν {I R}(F : (I ⊎ R) ▻ R){lX}(X : Pow I lX)(r : R) : Set (lI ⊔ lX) where
      coinductive
      constructor [_] 
      field       ]_[ : ⟦ % F r ⟧ X

  ⟦_⟧▻ : {I O : ★ lI} → I ▻ O → ∀ {lX} → Pow I lX → Pow O (lX ⊔ lI)
  ⟦ F ⟧▻ X o = ⟦ F o ⟧ X

  open ν public
\end{code}

\begin{code}
module Sized where

  open import Size public renaming (↑_ to ⇑_)

  mutual

    ⟦_⟧ : ∀ {I} → De I → ∀ {lX} → Pow I lX → Size → Set (lI ⊔ lX)

    ⟦ `1       ⟧ X _ = ⊤
    ⟦ L `× R   ⟧ X z = ⟦ L ⟧ X z × ⟦ R ⟧ X z

    ⟦ `I k     ⟧ X z = ^ lI (X k)
    ⟦ `Σ S T   ⟧ X z = Σ S λ s → ⟦ T s ⟧ X z
    ⟦ `Π S T   ⟧ X z = Π S λ s → ⟦ T s ⟧ X z
    ⟦ `μ F r   ⟧ X z = μ F X r z
    ⟦ `ν F r   ⟧ X z = ν F X r z
    ⟦ D `>>= F ⟧ X z = ⟦ D ⟧ (λ j → ⟦ F j ⟧ X z) z

    data μ {I R}(F : (I ⊎ R) ▻ R){lX}(X : Pow I lX)(r : R)
           : Size → Set (lI ⊔ lX) where
      [_] : {z : Size} → ⟦ % F r ⟧ X z → μ F X r (⇑ z)

    record ν {I R}(F : (I ⊎ R) ▻ R){lX}(X : Pow I lX)(r : R)
           (s : Size) : Set (lI ⊔ lX) where
      coinductive
      constructor [_] 
      field       ]_[ : {z : Size< s} → ⟦ % F r ⟧ X z

  ⟦_⟧▻ : {I O : Set lI} →
         I ▻ O → ∀ {lX} → Pow I lX → Size → Pow O (lI ⊔ lX)
  ⟦ F ⟧▻ X z o = ⟦ F o ⟧ X z

  open ν public
\end{code}

## Predicate lifting

### Box

\begin{code}
open Sized public

module Box where

  mutual

    □ : ∀ {I}(D : De I){lX}{X : Pow I lX}{lP}(P : Pow/ X lP) →
        ∀ {z} → ⟦ D ⟧ X z → Set (lI ⊔ lP)

    □ (`1      ) P      _  = ⊤
    □ (L `× R  ) P (l , r) = □ L P l × □ R P r

    □ (`I i    ) P     xs  = ^ lI (P (i , ↓ xs))
    □ (`Σ S T  ) P (s , t) = □ (T s) P t
    □ (`Π S T  ) P      f  = ∀ s → □ (T s) P (f s)
    □ (`μ F r  ) P  [ xs ] = □ (% F r) P xs
    □ (`ν F r  ) P     xs  = ■ F P r xs
    □ (D `>>= F) P     xs  = □ D (uc λ j → □ (F j) P) xs

    record ■ {I R}(F : I ⊎ R ▻ R)
             {lX}{X : Pow  I lX}{lP}(P : Pow/ X lP)
             (r : R){s}(xs : ⟦ `ν F r ⟧ X s) : Set (lI ⊔ lP) where
      coinductive
      constructor <_>
      field       >_< : {z : Size< s} → □ (% F r) P {z} ] xs [

open Box; open ■
\end{code}

### All

\begin{code}
module All where

  ◽ : ∀ {I : Set lI}{lX}{X : Pow I lX}{lP}{P : Pow/ X lP}
        (m : Π _ P) → ∀ D {z} xs → □ D P {z} xs

  ◽   m (`1      )          xs   = tt
  ◽   m (L `× R  )      (l , r)  = ◽ m L l , ◽ m R r

  ◽   m (`I i    )          xs   = ↑ (m (i , ↓ xs))
  ◽   m (`Σ S T  )      (s , t)  = ◽ m (T s) t
  ◽   m (`Π S T  )           f   = λ s → ◽ m (T s) (f s)
  ◽   m (`μ F r  ) ([_] {z} xs)  = ◽ m (% F r) {z} xs
  > ◽ m (`ν F r  )          xs < = ◽ m (% F r) ] xs [
  ◽   m (D `>>= F)          xs   = ◽ (uc λ j → ◽ m (F j)) D xs
\end{code}
