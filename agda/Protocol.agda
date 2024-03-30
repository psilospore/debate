-- Reference  https://github.com/google-deepmined/debate/blob/main/Debate/Protocol.lean

module Protocol where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)
open import Data.Bool using (Bool)
-- There is an alternative Vector should I use that?
open import Data.Vec using (Vec)
open import Foreign.Haskell.Either

-- We distinguish debater and verify oracles so that we can measure cost separately
-- for different agents.  We will plug in the same oracles in the end for all ids. -/
data OracleId : Set where
  AliceId : OracleId
  BobId : OracleId
  VeraId : OracleId

{- The state of a debate.  Either
    1. An uninterrupted Vector Bool n trace, or
    2. A final result if we rejected.

Lean def:
def State (n : ℕ) := Except Bool (Vector Bool n)
* TODO is there a statically sized list/array?
-}
State : ℕ → Set
State n = Either Bool (Vec Bool n)


{- Alice takes the transcript so far and estimates a probability that the next step is 1.
    In the game, Alice's goal is to produce output 1.  An honest Alice will try to mimic Oracle.fold.

Lean def:
def Alice' (o : OracleId) := (n : ℕ) → Vector Bool n → Comp {o} ℝ

TODO stub out computation Monad

-}

Alice' : OracleId → ℕ → Set
Alice' o n =  Vec Bool n → Comp o Float
