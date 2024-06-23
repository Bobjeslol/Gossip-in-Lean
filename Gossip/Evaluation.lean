-- Evaluation.lean
--
-- Author:      Timo Doherty
-- Student-ID:  11868910
-- Course:      Graduation Project Informatica
-- Date:        2024-06-23
--
-- Description:
-- - This file contains the evaluation of the gossip representation contained in Gossip/GossipSufficient.lean.
-- Evaluation is done in two ways:
-- - Using lemmas to prove properties of the gossip representation.
-- - Using manual evaluation to verify the gossip state after some sequence of calls.


import Gossip.GossipSufficient


-- Calling shares your own secret with the other agent.
lemma makeCall_shares_secrets : (makeCall (initialState n) (a, b)) a b := by
  simp [makeCall, initialState]


-- Old agents only know the secrets of old agents iff they did before.
lemma addAgent_old_old {s : GossipState n} {i j : Fin n} :
    addAgent s i.castSucc j.castSucc ↔ s i j := by
    simp [addAgent]


-- Old agents don't know the secrets of the new agents.
lemma addAgent_old_new {s : GossipState n} {i : Fin n} :
    ¬ addAgent s i.castSucc (Fin.last n) := by
    simp only [addAgent, beq_self_eq_true, Fin.lastCases_last, Fin.lastCases_castSucc,
      not_false_eq_true]


-- New agents don't know the secrets of the old agents.
lemma addAgent_new_old {s : GossipState n} {i : Fin n} :
    ¬ addAgent s (Fin.last n) i.castSucc := by
    simp [addAgent]
    cases i
    simp [Fin.castSucc, Fin.last]
    intro a
    subst a
    simp_all only [lt_self_iff_false]


-- New agents know their own secret.
lemma addAgent_new_new {s : GossipState n} :
    addAgent s (Fin.last n) (Fin.last n) := by
    simp [addAgent]


-- The gossip after some call sequence will still be available if we do another call first.
lemma knowledgePersistsCallBefore (n : ℕ) (σ : List (Call n)) (i j k l: Fin n) :
  (makeCalls (initialState n) σ) i j → (makeCalls (makeCall (initialState n) (k, l)) σ) i j := by
  intro h
  apply makeCalls_increases_gossip
  · exact makeCallMakesGossip (initialState n) (k, l)
  · exact h


-- The gossip in some state is still available after a call.
lemma knowledgePersistsCallAfter (n : ℕ) (i j k l: Fin n) (s : GossipState n) :
  s i j → (makeCall s (k, l)) i j := by
  simp [makeCall]
  intro h
  if h_eq : i = k then
    rw [if_pos h_eq]
    left
    exact h
  else
    rw [if_neg h_eq]
    if h_eq2 : i = l then
      rw [if_pos h_eq2]
      left
      exact h
    else
      rw [if_neg h_eq2]
      exact h


-- Initially agents know their own secrets.
lemma initially_knows_own_secret (n : ℕ) (i : Fin n) : initialState n i i := by
  simp [initialState]


-- Initially agents dont know each other's secrets.
lemma intially_no_secrets (n : ℕ) (i j : Fin n) : i ≠ j → ¬ (initialState n) i j := by
  simp [initialState]


-- Manual evaluation:
def calls : List (Call 4) := [(0, 1), (1, 2), (2, 3), (3, 0)]
def calls_big : List (Call 10) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9), (9, 0)]

#eval showState (makeCall (initialState 4) (0, 1))                          -- Correct
#eval showState (makeCall (makeCall (initialState 4) (0, 1)) (1, 2))        -- Correct
#eval showState (makeCalls (initialState 4) calls)                          -- Correct, 1 never learns the secret of 3
#eval showState (makeCalls (initialState 10) calls_big)                     -- Correct
