# Examples

\begin{code}
{-# OPTIONS --copatterns --sized-types #-}
module Ernesto.Examples where

open import AD
open import Ernesto; open Sized
\end{code}

`N z` is the carrier of the terminal coalgebra of the identity functor.

\begin{code}
NF : ⊤Z ▻ ⊤Z
NF = `ν (`I ∘ inr)

N = λ z → ⟦ NF ⟧▻ (λ _ → ⊤Z) z _
\end{code}

`n` is an inhabitant of `N z`, for any size z. Observationally it is
the unique element of `N`, but intensionally this does not hold.

\begin{code}
n : ∀ {z} → N z
] n [ = ↑ n
\end{code}

If we build another `N` in the same way Agda *decides* that it is
*not* definitionally equal to `n`: `id-nm` does not typecheck.

\begin{code}
m : ∀ {z} → N z
] m [ = ↑ m

-- id-nm : m ≡ n
-- id-nm = <>
\end{code}

Streams and conatural numbers.

\begin{code}
StreamF : ⊤Z ▻ ⊤Z
StreamF = `ν λ _ → `I (inl _) `× `I (inr _)

Stream : (A : Set) → Size → Set
Stream A = ⟦ StreamF _ ⟧ λ _ → A

CoNat = Stream ⊤

module _ {A} where

  length/ : ∀ {z} → Stream A z → CoNat z
  ] length/ xs [  = _ , ↑ (length/ xs)

  length : Stream A ∞ → CoNat ∞
  length xs = length/ xs
\end{code}
