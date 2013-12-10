# Examples

\begin{code}
{-# OPTIONS --copatterns --sized-types #-}
module Ernesto.Examples where

open import Mod.Base
open import Ernesto
\end{code}

`N` is the carrier of the terminal coalgebra of the identity functor.

\begin{code}
NF : [1] ▻ [1]
NF = `ν (`I ∘ inr)

N = ⟦ NF ⟧▻ (λ _ → [1]) ∞ _
\end{code}

`n` is an inhabitant of `N`. Observationally it is the unique element
of `N`, but intensionally this does not hold.

\begin{code}
n : N
] n [ = ↑ n
\end{code}

If we build another `N` in the same way Agda *decides* that it is
*not* definitionally equal to `n`. As we would expect, `id-nm` does
not typecheck.

\begin{code}
m : N
] m [ = ↑ m

-- id-nm : N ∋ n → N ∋ m
-- id-nm = id
\end{code}

Let's see whether we can discriminate.

\begin{code}
biased-observation : ∀ {z : N} → z ≡ [ ↑ z ] → [0]
biased-observation ()
\end{code}

This is not very encouraging: the point is that I think that
(compositions of) constructors for records that have an endo type
should not be distinguisable from identity.

Let's see some other examples.

\begin{code}
StreamF : [1] ▻ [1]
StreamF = `ν λ _ → `I (inl _) `× `I (inr _)

Stream : (A : Set) → Pow Size _
Stream A = ⟦ StreamF _ ⟧ λ _ → A

CoNat = Stream ⊤

module _ {A} where

  length/ : ∀ {z} → Stream A z → CoNat z
  ] length/ xs [  = _ , ↑ (length/ xs)

  length : Stream A ∞ → CoNat ∞
  length xs = length/ xs
\end{code}
