# Examples

\begin{code}
{-# OPTIONS --copatterns --sized-types #-}
module Ernesto.Examples where

open import AD
open import Ernesto; open Sized
\end{code}

`N` is the carrier of the terminal coalgebra of the identity functor.

\begin{code}
NF : ⊤Z ▻ ⊤Z
NF = `ν (`I ∘ inr)

N = ⟦ NF ⟧▻ (λ _ → ⊤Z) ∞ _
\end{code}

`n` is an inhabitant of `N`. Observationally it is the unique element
of `N`, but intensionally this does not hold.

\begin{code}
n : N
] n [ = ↑ n
\end{code}

If we build another `N` in the same way Agda *decides* that it is
*not* definitionally equal to `n`: `id-nm` does not typecheck.

\begin{code}
m : N
] m [ = ↑ m

open Manifest Z using (_∋_)

-- id-nm : N ∋ n → N ∋ m
-- id-nm = id
\end{code}

Thanks to Abel's fix to bug 1271, we cannot discriminate anymore
between `n` and `[ ↑ n ]`.

\begin{code}
-- former-bug : {n : N} → n ≡ [ ↑ n ] → [0]
-- former-bug ()
\end{code}

Streams and conatural numbers.

\begin{code}
StreamF : ⊤Z ▻ ⊤Z
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
