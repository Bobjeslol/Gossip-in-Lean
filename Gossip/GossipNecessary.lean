-- GossipNecessary.lean
--
-- Author:      Timo Doherty
-- Course:      Graduation Project Informatica
--
-- Description:
-- - This file implements the groundwork for the proof that 2n-4 calls are required
-- for all agents to become experts. The structure of this proof should follow
-- that of Baker and Shostak's approach `Gossips and telephones`.


import Gossip.GossipSufficient
import Mathlib.Data.List.Indexes
import Mathlib.Data.List.Basic


-- Given a sequence of length 2n-4 or less that makes all agents experts,
-- before each of the calls of the sequence, the agents in that call do
-- not know each other's secrets.
lemma noSelfHearing {n : Nat} : ∀ (σ : List (Call n)), σ.length ≤ 2 * n - 4
  → allExpert (makeCalls (initialState n) σ)
  → ∀ i : Fin σ.length,
  ¬ ((makeCalls (initialState n) (σ.take (i - 1))) σ[i].fst σ[i].snd
  ∨ (makeCalls (initialState n) (σ.take (i - 1))) σ[i].snd σ[i].fst) :=
  sorry


-- All sequences that make all n, with n ≥ 4 agents experts, have length 2n-4 or higher.
theorem necessity {n : Nat} : (n ≥ 4) →
  ∀ (σ : List (Call n)), allExpert (makeCalls (initialState n) σ)
  → σ.length ≥ 2*n - 4 := sorry
