# Issues with nested fixpoints

\begin{code}
{-# OPTIONS --copatterns  #-}
module Bad where
\end{code}

\begin{code}
open import AD
open import Ernesto; open Sized
\end{code}

## μ A. A

My expectation - Empty
Agda           - Empty

\begin{code}
μA,A : En ⊤Z
μA,A = `μ (`I ∘ inr)
\end{code}

\begin{code}
-- x : ⟦ μA,A _ ⟧ ⊥Z/ ∞
-- x = [ ↑ x ]
\end{code}

\begin{code}
no-μA,A : ¬ ⟦ μA,A _ ⟧ ⊥Z/ ∞
no-μA,A [ ↑ [ ↑ x ] ] = no-μA,A x
\end{code}

## ν A. A

My expectation - Inhabited
Agda           - Inhabited

\begin{code}
νA,A : En ⊤Z
νA,A = `ν (`I ∘ inr)
\end{code}

\begin{code}
x : ⟦ νA,A _ ⟧ ⊥Z/ ∞
↓ ] x [ = x
\end{code}

TODO. Tag the different variables by using manifests instead of `⊤Z`

## ν A. μ B. A

My expectation - Inhabited
Agda           - I cannot inhabit, I cannot prove empty

\begin{code}
νA,μB,A : En ⊤Z
νA,μB,A = `ν (`μ (`I ∘ inl ∘ inr))

-- ex2 : ∀ {z} → ⟦ νA,μB,A _ ⟧ ⊥Z/ z
-- xe2 : ∀ {z} → ⟦ %ν (`μ (`I ∘ inl ∘ inr)) tt ⟧ ⊥Z/ z
-- ] ex2 [ {z} = xe2
-- xe2     {z} = {!!}
\end{code}

\begin{code}
{-# NON_TERMINATING #-}
no-νA,μB,A : ¬ ⟦ νA,μB,A _ ⟧ ⊥Z/ ∞
no-νA,μB,A' : ¬ μ _ _ tt ∞
no-νA,μB,A p = no-νA,μB,A' ] p [
no-νA,μB,A' [ ↑ (↑ p) ] = no-νA,μB,A p
\end{code}

## μ A. ν B. A

My expectation - Empty
Agda           - Inhabited, I cannot prove it empty as well

\begin{code}
μA,νB,A : En ⊤Z
μA,νB,A = `μ (`ν (`I ∘ inl ∘ inr))

ex3 : ⟦ μA,νB,A _ ⟧ ⊥Z/ ∞
xe3 : ν (`I ∘ inl ∘ inr) _ _ ∞
ex3     = [ xe3 ]
] xe3 [ = ↑ ↑ ex3
\end{code}

## μ A. ν B. A × B

My expectation - Empty
Agda           - Inhabited

\begin{code}
μA,νX,A×X : En ⊤Z
μA,νX,A×X = `μ (`ν (`I ∘ inl ∘ inr ′× `I ∘ inr))

ex : ⟦ μA,νX,A×X _ ⟧ ⊥Z/ ∞
xe : ν ((`I ∘ inl ∘ inr) ′× (`I ∘ inr)) _ tt ∞
ex     = [ xe ]
] xe [ = ↑ ↑ ex , ↑ xe
\end{code}

IIRC in the Altenkirch-Danielsson DTP 2010 paper there is 

`μ A. ν B. 1 + A × B`
