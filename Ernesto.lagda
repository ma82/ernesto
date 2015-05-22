# A universe of functors closed under μ, ν and monadic composition

\begin{code}
{-# OPTIONS --copatterns --sized-types #-}
module Ernesto {lI} where
\end{code}

\begin{code}
open import AD hiding (■)
\end{code}

## Syntax

\begin{code}
infix 5 _`×_
infix 4 _`>>=_

data Er (I : ★ lI) : ★ (S lI) where

  `I     : (i : I)                       → Er I
  `Σ `Π  : (S : ★ lI)(T : S → Er I)      → Er I
  `μ `ν  : ∀ {R}(F : R → Er (I ⊎ R)) → R → Er I

  `1     :                                 Er I
  _`×_   : (L R : Er I)                  → Er I

  _`>>=_ : ∀ {J}(D : Er J)(F : J → Er I) → Er I

infix 0 _▻_
_▻_ = λ (I O : ★ lI) → O → Er I
En = λ I → I ▻ I

infix 5 _′×_
_′×_ : ∀ {I O} → I ▻ O → I ▻ O → I ▻ O
(L ′× R) o = L o `× R o
\end{code}

\begin{code}
_`+_ : ∀ {I}(L R : Er I) → Er I
L `+ R = `Σ (⊤I ⊎ ⊤I) ⊎.[ (λ _ → L) , (λ _ → R) ] where ⊤I = ⊤ {lI}

`K : Set lI → ∀ {I} → Er I
`K X = `Σ X λ _ → `1
\end{code}

\begin{code}
`return : {I : ★ lI} → I → Er I
`return = `I

`map : {I J : ★ lI} → (I → J) → Er I → Er J
`map f D = D `>>= `return ∘ f
\end{code}

\begin{code}
data FMTags : Set lI where roll var : FMTags

_✴ : ∀ {I} → En I → I ⊎ I ▻ I
(F ✴) i = `Σ FMTags λ { var  → `I (inl i)    
                      ; roll → `map inr (F i) }
\end{code}

\begin{code}
μ✴ ν✴ : ∀ {I} → En I → I ▻ I
μ✴ F = `μ (F ✴) 
ν✴ F = `ν (F ✴)
\end{code}
                            
\begin{code}
_`∘_ : {A B C : ★ lI} → B ▻ C → A ▻ B → A ▻ C
(F `∘ G) a = F a `>>= G

`_[_] : {I J K : ★ lI} → I ⊎ K ▻ J → I ▻ K → I ▻ J
` F [ G ] = F `∘ ⊎.[ `I , G ]

%μ : {I J : ★ lI} → I ⊎ J ▻ J → I ▻ J
%μ F = ` F [ `μ F ]

%ν : {I J : ★ lI} → I ⊎ J ▻ J → I ▻ J
%ν F = ` F [ `ν F ]
\end{code}

## Semantics

\begin{code}
module Unsized where

  mutual

    ⟦_⟧ : ∀ {I} → Er I → ∀ {lX} → Pow I lX → Set (lI ⊔ lX)

    ⟦ `I k     ⟧ X = ^ lI (X k)
    ⟦ `Σ S T   ⟧ X = Σ S λ s → ⟦ T s ⟧ X
    ⟦ `Π S T   ⟧ X = Π S λ s → ⟦ T s ⟧ X
    ⟦ `μ F r   ⟧ X = μ F X r
    ⟦ `ν F r   ⟧ X = ν F X r

    ⟦ `1       ⟧ X = ⊤
    ⟦ L `× R   ⟧ X = ⟦ L ⟧ X × ⟦ R ⟧ X

    ⟦ D `>>= F ⟧ X = ⟦ D ⟧ λ j → ⟦ F j ⟧ X

    data μ {I R}(F : (I ⊎ R) ▻ R){lX}(X : Pow I lX)(r : R) : Set (lI ⊔ lX) where
      [_] : ⟦ %μ F r ⟧ X → μ F X r

    record ν {I R}(F : (I ⊎ R) ▻ R){lX}(X : Pow I lX)(r : R) : Set (lI ⊔ lX) where
      coinductive
      constructor [_] 
      field       ]_[ : ⟦ %ν F r ⟧ X

  ⟦_⟧▻ : {I O : ★ lI} → I ▻ O → ∀ {lX} → Pow I lX → Pow O (lX ⊔ lI)
  ⟦ F ⟧▻ X o = ⟦ F o ⟧ X

  open ν public
\end{code}

\begin{code}
module Sized where

  open import Size public renaming (↑_ to ⇑_)

  mutual

    ⟦_⟧ : ∀ {I} → Er I → ∀ {lX} → Pow I lX → Size → Set (lI ⊔ lX)

    ⟦ `1       ⟧ X _ = ⊤
    ⟦ L `× R   ⟧ X z = ⟦ L ⟧ X z × ⟦ R ⟧ X z

    ⟦ `I k     ⟧ X z = ^ lI (X k)
    ⟦ `Σ S T   ⟧ X z = Σ S λ s → ⟦ T s ⟧ X z
    ⟦ `Π S T   ⟧ X z = Π S λ s → ⟦ T s ⟧ X z
    ⟦ `μ F r   ⟧ X z = μ F X r z
    ⟦ `ν F r   ⟧ X z = ν F X r z
    ⟦ D `>>= F ⟧ X z = ⟦ D ⟧ (λ j → ⟦ F j ⟧ X z) z

    data μ {I R}(F : (I ⊎ R) ▻ R){lX}(X : Pow I lX)(r : R)(s : Size)
           : Set (lI ⊔ lX) where
      [_] : {z : Size< s} → ⟦ %μ F r ⟧ X z → μ F X r s

    record ν {I R}(F : (I ⊎ R) ▻ R){lX}(X : Pow I lX)(r : R)(s : Size)
             : Set (lI ⊔ lX) where
      coinductive
      constructor [_] 
      field       ]_[ : {z : Size< s} → ⟦ %ν F r ⟧ X z

  ⟦_⟧▻ : {I O : Set lI} →
         I ▻ O → ∀ {lX} → Pow I lX → Size → Pow O (lI ⊔ lX)
  ⟦ F ⟧▻ X z o = ⟦ F o ⟧ X z

  open ν public
\end{code}

\begin{code}
  ⟦_⟧map : ∀ {I : Set lI}{lX lY}{X : Pow I lX}{Y : Pow I lY} → ∀ D →
           (X ⇛ Y) → ∀ {z} → ⟦ D ⟧ X z → ⟦ D ⟧ Y z
  ⟦_⟧map (`I i)     f   xs      = ↑ (f i (↓ xs))
  ⟦_⟧map (`Σ S T)   f (s , t)   = s , ⟦ T s ⟧map f t
  ⟦_⟧map (`Π S T)   f    g    s = ⟦ T s ⟧map f (g s)
  ⟦_⟧map (`μ F x)   f [ xs ]    = [ ⟦ F x ⟧map ⊎.[ (λ i x → ↑ f i (↓ x))
                                                 , (λ r → ⟦ `μ F r ⟧map f) ]   xs ]
  ] ⟦_⟧map (`ν F x) f   xs [    =   ⟦ F x ⟧map ⊎.[ (λ i x → ↑ f i (↓ x))
                                                 , (λ r → ⟦ `ν F r ⟧map f) ] ] xs [
  ⟦_⟧map  `1        f   xs      = tt
  ⟦_⟧map (L `× R)   f (ls , rs) = ⟦ L ⟧map f ls , ⟦ R ⟧map f rs
  ⟦_⟧map (D `>>= F) f xs        = ⟦ D ⟧map (λ a → ⟦ F a ⟧map f) xs
\end{code}

## Box

\begin{code}
  module Box where

    mutual

      □ : ∀ {I}(D : Er I){lX}{X : Pow I lX}{lP}(P : Pow/ X lP) →
          ∀ {z} → ⟦ D ⟧ X z → Set (lI ⊔ lP)

      □ (`1      ) P      _  = ⊤
      □ (L `× R  ) P (l , r) = □ L P l × □ R P r

      □ (`I i    ) P     xs  = ^ lI (P (i , ↓ xs))
      □ (`Σ S T  ) P (s , t) = □ (T s) P t
      □ (`Π S T  ) P      f  = ∀ s → □ (T s) P (f s)
      □ (`μ F r  ) P  [ xs ] = □ (%μ F r) P xs
      □ (`ν F r  ) P     xs  = ■ F P r xs
      □ (D `>>= F) P     xs  = □ D (uc λ j → □ (F j) P) xs

      record ■ {I R}(F : I ⊎ R ▻ R)
               {lX}{X : Pow  I lX}{lP}(P : Pow/ X lP)
               (r : R){s}(xs : ⟦ `ν F r ⟧ X s) : Set (lI ⊔ lP) where
        coinductive
        constructor <_>
        field       >_< : {z : Size< s} → □ (%ν F r) P {z} ] xs [

  open Box; open ■
\end{code}

\begin{code}
  ◽ : ∀ {I : Set lI}{lX}{X : Pow I lX}{lP}{P : Pow/ X lP}
        (m : Π _ P) → ∀ D {z} xs → □ D P {z} xs

  ◽   m (`1      )          xs   = tt
  ◽   m (L `× R  )      (l , r)  = ◽ m L l , ◽ m R r

  ◽   m (`I i    )          xs   = ↑ (m (i , (↓ xs)))
  ◽   m (`Σ S T  )      (s , t)  = ◽ m (T s) t
  ◽   m (`Π S T  )           f   = λ s → ◽ m (T s) (f s)
  ◽   m (`μ F r  ) ([_] {z} xs)  = ◽ m (%μ F r) {z} xs
  > ◽ m (`ν F r  )          xs < = ◽ m (%ν F r) ] xs [
  ◽   m (D `>>= F)          xs   = ◽ (uc λ j → ◽ m (F j)) D xs
\end{code}

