-- gossip.lean
--
-- Author:      Timo Doherty
-- Student-ID:  11868910
-- Course:      Graduation Project Informatica
-- Date:        2024-06-13
-- Description:
-- - This file contains the representation of gossip in Lean. The definitions provided
-- are used to formalize the efficient gossip algorithm for complete graphs, that state
-- that for (n ≥ 4) there is a call sequence of length 2n - 4 that makes everyone an expert.
--
-- TODO: Add more comments, clean up code, finalize proofs, add more lemmas, add more tests.
-- TODO: Add the definition of the necessity property, and structure it using sorry.


import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Matrix.Notation

variable {n : ℕ}

-- State representation that contains the all gossip information between any agents.
def GossipState (n : Nat) : Type := Fin n → Fin n → Prop

-- A Call is a pair of agents.
def Call (n : Nat): Type := Fin n × Fin n

-- Generates the initial state where agents only know their own secret.
def initialState (n : Nat) : GossipState n := fun i j => i = j

instance {n : ℕ} : DecidableRel (initialState n) := decEq

-- Check if an agent is an expert.
def isExpert (s : GossipState n) (i : Fin n): Prop := ∀ j, s i j

instance {s : GossipState n} [DecidableRel s] {i : Fin n} : Decidable (isExpert s i) :=
  Fintype.decidableForallFintype

-- Check if all agents are experts.
def checkIfEE (s : GossipState n) : Prop := ∀ i, isExpert s i

instance {s : GossipState n} [DecidableRel s] : Decidable (checkIfEE s) :=
  Fintype.decidableForallFintype

-- Executes a single call.
def makeCall (s : GossipState n) : Call n → GossipState n
  | (i, j), x, y =>
    if x = i
    then s x y ∨ s j y
    else
      if x = j
        then s x y ∨ s i y
        else s x y

instance {s : GossipState n} [DecidableRel s] : ∀ {c : Call n}, DecidableRel (makeCall s c)
| (i, j), x, y =>
    if h : x = i
      then decidable_of_iff (s i y ∨ s j y) (by simp [makeCall, h])
      else
        if h' : x = j
          then decidable_of_iff (s j y ∨ s i y) (by cases h'; simp [makeCall, h])
          else decidable_of_iff (s x y) (by simp [makeCall, h, h'])

-- Executes multiple calls sequentially.
def makeCalls (s : GossipState n) (cs : List (Call n)) : GossipState n :=
  cs.foldl makeCall s

instance {s : GossipState n} [DecidableRel s] {cs : List (Call n)} :
    DecidableRel (makeCalls s cs) := by
  induction cs generalizing s
  case nil hs => exact hs
  case cons c _ ih hs => exact ih


-- Rather than making a repr instance for GossipState, its easier to assume s is decidable and use repr.
def showState (s : GossipState n) [DecidableRel s] : Lean.Format :=
    repr (fun i j => if s i j then "True " else "False")


-- Evaluation purposes
--------------------------------------------------------------------------------

#eval showState (makeCall (initialState 4) (0, 1))
#eval showState (makeCall (makeCall (initialState 4) (0, 1)) (1, 2))
def calls : List (Call 4) := [(0, 1), (1, 2), (2, 3), (3, 0)]
#eval showState (makeCalls (initialState 4) calls)
def calls_big : List (Call 10) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9), (9, 0)]
#eval showState (makeCalls (initialState 10) calls_big)

--------------------------------------------------------------------------------


-- Prop: All gossip that is known in s1 is also known in s2.
def moreGossip (s1 s2 : GossipState n) : Prop := ∀ a b : Fin n, (s1 a b) → (s2 a b)


-- Adds an agent to a state, that knows only their own secret
def addAgent (s : GossipState n) : GossipState (n.succ) :=
  λ a b => Fin.lastCases (b == Fin.last n)
                         (fun i => Fin.lastCases (false)
                                                 (fun b => s i b)
                                                b) a

-- Same call contents, but different type to match the larger state.
def expandCall {n : ℕ} (c : Call n) : Call (Nat.succ n) :=
  match c with
    | (i, j) => (i, j)

-- Expands a list of calls to the larger state.
def expandCalls {n : ℕ} (cs : List (Call n)) : List (Call (Nat.succ n)) :=
  cs.map expandCall

-- Verifies whether a list of calls contains a specific call.
def containsAdjusted {n : Nat} (σ : List (Call n)) (c : Fin (n + 1) × Fin (n + 1)) : Bool :=
  σ.any (match c with
          | (i, j) => λ c => (c.1 = i ∧ c.2 = j) ∨ (c.1 = j ∧ c.2 = i))

-- Two states are identical if they contain the same gossip.
def stateEquivalence : GossipState n → GossipState n → Prop :=
  λ s1 s2 => ∀ a b, s1 a b ↔ s2 a b


-- Calling shares your own secret with the other agent.
lemma makeCall_shares_secrets : (makeCall (initialState n) (a, b)) a b := by
  simp [makeCall, initialState]


-- Being called by an expert means becoming an expert.
lemma expert_makes_expert {s : GossipState n} {i j : Fin n} :
  isExpert s i → isExpert (makeCall s (i, j)) j := by
  unfold isExpert
  intro h j_1
  simp [makeCall]
  simp_all only [or_true, ite_self]


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


-- Makecalls is the same as makeCall on head followed by makeCalls on tail.
lemma makeCalls_cons (s : GossipState n) (c : Call n) (cs : List (Call n)) :
  makeCalls s (c :: cs) = makeCalls (makeCall s c) cs := by
    rfl


-- Makecalls is the same as makeCalls on init followed by makeCall on last.
lemma makeCalls_snoc (s : GossipState n) (cs : List (Call n)) (c : Call n) :
  makeCalls s (cs ++ [c]) = makeCall (makeCalls s cs) c := by
    induction cs generalizing s
    case nil =>
      rfl
    case cons c' cs ih =>
      simp [makeCalls, ih]


-- Adding the same call to two states means the gossip relation remains.
lemma makeCall_increases_gossip (s1 s2 : GossipState n) (c : Call
n) : moreGossip s1 s2 → moreGossip (makeCall s1 c) (makeCall s2 c) := by
    intro h a b -- There's gotta be a nicer way of doing this.
    simp [makeCall]
    intro a_1
    simp_all only
    split
    simp_all only
    split
    rename_i h_1
    subst h_1
    simp_all only [↓reduceIte]
    cases a_1
    · apply Or.inl
      apply h
      simp_all only
    · apply Or.inr
      apply h
      simp_all only
    simp_all only [↓reduceIte]
    split
    · rename_i a_j
      subst a_j
      simp_all only [↓reduceIte]
      cases a_1
      · apply Or.inl
        apply h
        simp_all only
      · apply Or.inr
        apply h
        simp_all only
    · simp_all only [↓reduceIte]
      apply h
      simp_all only


-- Adding the same calls to two states means the gossip relation remains.
lemma makeCalls_increases_gossip (s1 s2 : GossipState n) (cs : List (Call n)) :
    moreGossip s1 s2 → moreGossip (makeCalls s1 cs) (makeCalls s2 cs) := by
    intro h
    induction cs generalizing s1 s2
    case nil =>
      simp [makeCalls]
      exact h
    case cons head tail ih =>
      rw [makeCalls_cons, makeCalls_cons]
      have h_call : moreGossip (makeCall s1 head) (makeCall s2 head) :=
        makeCall_increases_gossip s1 s2 head h
      exact ih (makeCall s1 head) (makeCall s2 head) h_call


-- Adding a call to a state doesn't decrease the amount of gossip.
lemma makeCall_makes_gossip (s : GossipState n) (c : Call n) :
    moreGossip s (makeCall s c) := by
  unfold moreGossip
  intro a b h
  simp [makeCall]
  simp_all only
  split
  simp_all only
  split
  rename_i h_1
  subst h_1
  simp_all only [true_or]
  rename_i c f g i j k
  if hyp: a = j then
    rw [hyp, if_pos]
    subst hyp
    simp_all only [true_or]
    rfl
  else
    rw [if_neg]
    simp_all only
    exact hyp


-- Adding calls to a state don't decrease the amount of gossip.
lemma calls_increase_gossip (s : GossipState n) (cs : List (Call n)) :
    moreGossip s (makeCalls s cs) := by
    induction cs generalizing s
    case nil =>
      simp [makeCalls]
      unfold moreGossip
      intro a b h
      exact h
    case cons c cs ih =>
      rw [makeCalls_cons]
      have l : moreGossip s (makeCall s c) := by
        apply makeCall_makes_gossip -- uses the previous lemma for a single call.
      simp_all [moreGossip]


-- The gossip after some call sequence will still be available if we do another call first.
-- Unused, but nice for evaluation.
lemma knowledge_persists_call_before (n : ℕ) (σ : List (Call n)) (i j k l: Fin n) :
  (makeCalls (initialState n) σ) i j → (makeCalls (makeCall (initialState n) (k, l)) σ) i j := by
  intro h
  apply makeCalls_increases_gossip
  · exact makeCall_makes_gossip (initialState n) (k, l)
  · exact h


-- The gossip in some state is still available after a call.
-- Unused, but nice for evaluation.
lemma knowledge_persists_call_after (n : ℕ) (i j k l: Fin n) (s : GossipState n) :
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


-- Unused, maybe good for evaluation purposes
-- If two states are equal and they both contain a call at the start, then the states without the call are equal
lemma makeCall_same_state (s1 s2 : GossipState n) (c : Call n) :
  stateEquivalence (makeCall s1 c) (makeCall s2 c) → stateEquivalence s1 s2 := by
  sorry


-- After some arbitrary call sequence, the same information is still available.
-- Unused, maybe good for evaluation purposes
lemma knowledge_persists_calls_after (n : ℕ) (σ : List (Call n)) (i j k l: Fin n) :
  (makeCall (initialState n) (k, l) i j) →
  (makeCalls (makeCall (initialState n) (k, l)) σ) i j := by
  sorry


-- Shows that secrets are not lost if calls are added before or after.
-- Unused, more general vresion good for evaluation purposes
lemma knowledge_persistence {n : ℕ} (σ τ : List (Call n)) (i j : Fin n) :
  (makeCalls (initialState n) σ i j) →
  (makeCalls (initialState n) (τ ++ σ) i j) ∧ (makeCalls (initialState n) (σ ++ τ) i j) := by
  intro h
  induction τ
  case nil =>
    simp
    exact h
  case cons =>
    sorry


-- States that adding an agent to a state doesn't decrease the amount of gossip
-- Unused, maybe good for evaluation purposes
lemma addAgent_doesnt_decrease_gossip (s1 s2 : GossipState n) :
  moreGossip s1 s2 → moreGossip (addAgent s1) (addAgent s2) := by
  intro h
  intro a b
  simp [addAgent]
  intro h1
  sorry


-- Adding an agent at the start contains more or the same gossip as adding an agent at the end
-- Unused, maybe good for evaluation purposes
lemma addAgent_increases_gossip (s : GossipState n) (σ : List (Call n)) (τ : List (Call (Nat.succ n))) :
  τ = expandCalls σ → moreGossip (makeCalls (addAgent s) (expandCalls σ)) (addAgent (makeCalls  s σ)) := by
  induction σ
  case nil =>
    sorry
  case cons =>
    sorry


-- An expert in the old state knows all but the new agent's secret if an agent is added.
lemma addAgent_expert_old {s : GossipState n} {i : Fin n} :
  isExpert s i ↔ ∀ j : Fin n, addAgent s i.castSucc j.castSucc := by
  have h1 : isExpert s i → ∀ j : Fin n, addAgent s i.castSucc j.castSucc := by
    intro h
    simp [addAgent]
    apply h
  have h2 : (∀ j : Fin n, addAgent s i.castSucc j.castSucc) → isExpert s i := by
    intro h
    unfold isExpert
    intro j
    simp [addAgent] at h
    exact h j
  exact Iff.intro h1 h2


-- Very messy, needs to be cleaned up.
-- We can replace addAgent with initialState (n + 1) in the following lemma n ≥ 4
lemma addAgent_equals_succ {n : ℕ} :
  addAgent (initialState n) = (initialState (Nat.succ n)) := by
  induction n
  case zero =>
    simp [addAgent, initialState]
    unfold initialState
    unfold addAgent
    simp
    unfold Fin.last
    simp_all
    funext
    funext
    aesop? -- what does this aesop do?
    case mp =>
      ext
      simp_all only [Fin.isValue, Fin.coe_fin_one]
    case mpr =>
      have h : x_1 = 0 := by
        rw [← Nat.one_eq_succ_zero] at x_1
        ext
        simp_all only [Fin.coe_fin_one, Fin.isValue]
      rw [h]
      simp [Fin.lastCases_last]
      simp [Fin.lastCases]
      unfold Fin.reverseInduction
      simp
      let t : Fin.last 0 = 0 := by
        unfold Fin.last
        simp
      rw [← t]
      simp
  case succ k ih =>
    unfold addAgent
    simp [ih]
    unfold initialState
    funext i
    cases i
    simp_all only [Fin.castSucc, Fin.last]
    case h.mk =>
      simp [Fin.lastCases, Fin.reverseInduction]
      rename_i val isLt
      split
      · simp_all only
        ext
        apply Iff.intro
        · intro a
          subst a
          apply Eq.refl
        · intro a
          subst a
          apply Eq.refl
      · ext
        apply Iff.intro
        · intro a
          simp_all only [Fin.eta, not_false_eq_true]
        · intro a
          subst a
          simp_all only [not_false_eq_true, and_self]


-- addAgent (initialState n) is replacable with initialState (n + 1) in the following lemma
lemma makeCalls_addAgent_initialState_equiv {n : Nat} (initial_call : Call (n + 1)) (expandedSeq : List (Call (n + 1))) :
  makeCall (makeCalls (makeCall (addAgent (initialState n)) initial_call) expandedSeq) initial_call =
  makeCalls (initialState (n + 1)) ([initial_call] ++ expandedSeq ++ [initial_call]) := by
  rw [← makeCalls_cons, addAgent_equals_succ, makeCalls_snoc]
  simp_all only [List.singleton_append]


-- Adding an agent before a call is equivalent to adding an agent after the call if the call doesn't involve the new agent
lemma addAgent_equiv_call {n : Nat} (c : Call n) (i : Fin n) :
  (c.1 ≠ i) ∧ (c.2 ≠ i) → makeCall (addAgent (initialState n)) (expandCall c) = addAgent (makeCall (initialState n) c) := by
  intro h
  cases h
  simp [expandCall, addAgent, initialState]
  simp_all only [ne_eq, not_false_eq_true]
  cases c
  rename_i a b
  unfold makeCall
  simp
  unfold initialState
  unfold addAgent
  simp
  apply funext
  aesop? -- What does this aesop do? Not a good approach...
  · simp [Fin.lastCases, Fin.reverseInduction]
    aesop?
  · simp [Fin.lastCases, Fin.reverseInduction]
    aesop? -- This is horrendous, but it works.
  · simp [Fin.lastCases, Fin.reverseInduction]
    aesop?


-- Expandcalls is equivalent to expandCall head ++ expandCalls tail
lemma expandCalls_equiv_expandCall {n : Nat} (c : Call n) (cs : List (Call n)) :
  expandCalls (c :: cs) = expandCall c :: expandCalls cs := by
  rfl


-- USED, UNFINISHED!
-- Adding an agent at the end is equivalent to adding an agent at the start if the sequence doesn't contain calls to the new agent
lemma addAgent_equiv_calls {n : Nat} (σ : List (Call n)) (i : Fin n) :
  (¬ containsAdjusted σ (i, Fin.last n)) ∧ (¬ containsAdjusted σ (Fin.last n, i)) →
  stateEquivalence (makeCalls (addAgent (initialState n)) (expandCalls σ)) (addAgent (makeCalls (initialState n) σ)) := by
  intro h
  induction σ
  case nil =>
    intro h
    intro b
    simp_all only [Bool.not_eq_true]
    apply Iff.intro
    · intro a
      exact a
    · intro a
      exact a
  case cons =>
    intro h'
    rw [expandCalls_equiv_expandCall, makeCalls_cons, addAgent_equiv_call]
    · rename_i head tail ih
      rw [makeCalls_cons]
      sorry

    · exact i

    · sorry


-- Main lemma for the induction step
lemma inductive_case (k : Nat) (h: Nat.succ k + 4 ≥ 4) (seq : List (Call (k + 4))):
    checkIfEE (makeCalls (initialState (k + 4)) seq) →
    ∃ seq', seq'.length = 2 + seq.length ∧ checkIfEE (makeCalls (initialState (Nat.succ k + 4)) seq') := by
  intro IH
  let expandedSeq := expandCalls seq
  let zero_fin : Fin (Nat.succ (k + 4)) := 0
  let succ_fin : Fin (Nat.succ (k + 4)) := Fin.last (k + 4)
  let initial_call : Call (Nat.succ (k + 4)) := (zero_fin, succ_fin)
  let attempt := makeCall (addAgent (initialState (k + 4))) initial_call
  let new_state := makeCall (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) expandedSeq) initial_call

  have single_calls : new_state = makeCalls (initialState (Nat.succ (k + 4))) ([initial_call] ++ expandedSeq ++ [initial_call]) := by
    simp [new_state]
    apply makeCalls_addAgent_initialState_equiv

  let calls_without_final_call := [initial_call] ++ expandedSeq
  let temp_state := makeCalls (addAgent (initialState (k + 4))) calls_without_final_call

  have milestone_1 : ∀ i, i ≠ succ_fin → temp_state zero_fin i := by
    unfold checkIfEE at IH

    have h : ∀ i, i ≠ succ_fin → makeCalls (addAgent (initialState (k + 4))) expandedSeq zero_fin i := by
      simp_all only [expandedSeq, isExpert]
      let zero_fin_old := 0
      have statement := IH (zero_fin_old)
      have h' : isExpert (makeCalls (initialState (k + 4)) seq) zero_fin_old := by
        simp_all only [new_state, succ_fin, expandedSeq]
        apply IH

      rw [addAgent_expert_old] at h' -- big step
      simp [succ_fin]

      have test := addAgent_equiv_calls seq (k + 4) (?_) -- look at this goal first
      simp [stateEquivalence] at test

      apply Fin.lastCases
      · intro a
        simp_all only [le_add_iff_nonneg_left, zero_le, Nat.cast_zero]
      · intro i a
        simp_all only [Nat.cast_zero, Fin.castSucc_zero, zero_fin_old]
      -- how to prove the call sequence with type List (Call n) where call is fin n x fin n doesnt contain any fin.last n?
      sorry

    -- New_state contains more gossip than temp_state.
    have h' : moreGossip (makeCalls (addAgent (initialState (k + 4))) expandedSeq) temp_state := by
      simp [temp_state, calls_without_final_call, expandedSeq]
      rw [addAgent_equals_succ, makeCalls_cons]
      apply makeCalls_increases_gossip
      unfold moreGossip
      intro a b
      apply makeCall_makes_gossip
    intro i a
    simp_all only [ne_eq, new_state, initial_call, zero_fin, succ_fin, expandedSeq]
    apply h'
    simp_all only [not_false_eq_true]

  -- The first agent learns the secret of the new agent as well due to the initial call
  have milestone_2 : temp_state zero_fin succ_fin := by
    simp [temp_state, calls_without_final_call, expandedSeq]
    rw [makeCalls_cons]
    have l : moreGossip (makeCall (addAgent (initialState (k + 4))) initial_call) (makeCalls ((makeCall (addAgent (initialState (k + 4))) initial_call)) (expandCalls seq)) := by
      apply calls_increase_gossip
    apply l
    simp [initial_call, makeCall]
    right
    simp [addAgent, initialState]
    simp_all only [Fin.lastCases_last, new_state, zero_fin, succ_fin]

  -- Thus the first agent is an expert
  have milestone_3 : isExpert temp_state zero_fin := by
    unfold isExpert
    simp [succ_fin] at milestone_2
    simp [temp_state]
    intro j
    have h1 : j ≠ succ_fin → temp_state zero_fin j := by
      exact milestone_1 j
    have h2 : j = succ_fin → temp_state zero_fin j := by
      intro h
      rw [h]
      exact milestone_2
    by_cases (j = succ_fin)
    · rename_i l
      simp [temp_state] at h2
      exact h2 l
    · rename_i l
      simp [temp_state] at h1
      exact h1 l

  -- Putting milestone_1 and milestone_2 together, we get that all but the last agents are experts
  have milestone_4 : ∀ i, i ≠ succ_fin → isExpert new_state i := by
    have subgoal_1 : makeCall (initialState (Nat.succ (k + 4))) initial_call zero_fin succ_fin := by
      apply makeCall_shares_secrets

    -- for all a, b where a != succ_fin, a knows b
    have subgoal_2 : ∀ i, i ≠ succ_fin → ∀ j, temp_state i j := by
      intro i h
      simp [temp_state, calls_without_final_call, expandedSeq]
      simp [checkIfEE] at IH
      have h' : isExpert (makeCalls (initialState (k + 4)) seq) i := by
        apply IH
      -- Need to introduce new agent's secret.
      rw [addAgent_expert_old] at h'
      -- This is tricky, might need a lemma that shows the polar secrets are shared identically after the initial call.
      sorry

    simp [new_state, isExpert]

    have subgoal_3 : moreGossip temp_state new_state := by
      simp [temp_state, new_state, calls_without_final_call, expandedSeq]
      apply makeCall_makes_gossip

    intro i a j
    simp_all only [ne_eq, new_state]
    apply subgoal_3
    simp_all only [not_false_eq_true]

  -- Using the final call, we can show that the new agent also becomes an expert
  have h_new4 : isExpert new_state succ_fin := by
    have h : isExpert temp_state zero_fin := by
      unfold isExpert
      intro j
      simp_all only [temp_state, calls_without_final_call]
      have expert : isExpert temp_state zero_fin := by
        exact milestone_3
      simp_all only [List.singleton_append]
      apply milestone_3

    have h' : new_state = makeCall temp_state initial_call := by
      rw [single_calls]
      simp [temp_state, calls_without_final_call, expandedSeq]
      repeat rw [makeCalls_cons]
      rw [makeCalls_snoc, addAgent_equals_succ]
    rw [h']
    apply expert_makes_expert
    exact h

  -- putting milestone_4 and h_new4 together, we get that everyone is an expert
  have milestone_5 : checkIfEE new_state := by
    unfold checkIfEE
    intro i
    cases i
    rename_i val isLt
    let i_rebuilt : Fin (Nat.succ (k + 4)) := ⟨val, isLt⟩
    by_cases (i_rebuilt = succ_fin);
    · simp_all only [i_rebuilt]
    · simp_all only [ne_eq, not_false_eq_true]

  -- So the sequence below suffices.
  exists [initial_call] ++ expandedSeq ++ [initial_call]
  rw [single_calls] at milestone_5
  constructor
  · simp_all
    unfold_let expandedSeq
    simp_all only [expandCalls, List.length_map, Nat.succ_add, zero_add]
  · exact milestone_5

-- induction for n > 3, base case n = 4
theorem expertSequenceWorks (n : Nat) : (n ≥ 4) → ∃ (seq : List (Call n)), seq.length = (2 * n - 4) ∧ checkIfEE (makeCalls (initialState n) seq) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | 2 => by simp
  | 3 => by simp
  | (m + 4) =>  by
                intro h
                induction m
                case zero =>
                  simp at h
                  exists [(0, 1), (2, 3), (0, 2), (1, 3)]
                case succ k IH =>
                  simp at IH
                  rcases IH with ⟨seq, claim⟩
                  have length : seq.length = 2 * (k + 4) - 4 := by
                    exact claim.left
                  have add_two_still_2nmin4 : 2 + seq.length = 2 * (Nat.succ (k + 4)) - 4 := by
                    rw [length]
                    simp_all only [Nat.succ_add, ge_iff_le, true_and, zero_add]
                    apply Eq.refl
                  rw [← add_two_still_2nmin4]
                  exact inductive_case k h seq claim.right