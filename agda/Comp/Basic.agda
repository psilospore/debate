module Comp.Basic where

open import Data.Bool
open import Data.Nat
open import Data.Vec
open import Data.List


{-
## Oracle-relative probabilitistic computations

`Prob α` represents the result of a probabilistic computation, but has no information about
how long the computation took.  `Comp s α` is a computation that is allowed to consult any
oracle `o ∈ s`, and produces a distribution over results and calls to each oracle.
TODO I don't know if we can even have probablistic computation in Agda but not sure.
Update decided to create a more simplified proof that doesn't depend on probabilistic computations.
-}

-- Define OracleId and Prob
-- ...

-- Define the Comp type
data Comp {I : Set} : List I → Set → Set
data Comp {I : Set} (s : List I) (α : Set) where
  pure'   : α → Comp s α
  sample' : {β : Set} → Prob β → (β → Comp s α) → Comp s α
  query'  : (o : I) → o ∈ s → (n : ℕ) → Vec Bool n → Comp s α → Comp s α → Comp s α
