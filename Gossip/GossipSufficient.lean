-- GossipSufficient.lean
--
-- Author:      Timo Doherty
-- Course:      Graduation Project Informatica
--
-- Description:
-- - This file contains the representation of gossip in Lean. The definitions provided
-- are used to formalize the efficient gossip algorithm for complete graphs, that state
-- that for (n ≥ 4) there is a call sequence of length 2n - 4 that suffices in the goal
-- of making each agent learn each other secret (becoming an expert).


import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.List.Indexes

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

-- Instance that allows isExpert to evaluate on Decidable GossipStates.
instance {s : GossipState n} [DecidableRel s] {i : Fin n} : Decidable (isExpert s i) :=
  Fintype.decidableForallFintype

-- Check if all agents are experts.
def allExpert (s : GossipState n) : Prop := ∀ i, isExpert s i

-- Instance that allows allExpert to evaluate on Decidable GossipStates.
instance {s : GossipState n} [DecidableRel s] : Decidable (allExpert s) :=
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

-- Instance that allows Decidable GossipStates built with makeCall to be decidable.
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

-- Instance that allows Decidable GossipStates built with makeCalls to be decidable.
instance {s : GossipState n} [DecidableRel s] {cs : List (Call n)} :
    DecidableRel (makeCalls s cs) := by
  induction cs generalizing s
  case nil hs => exact hs
  case cons c _ ih hs => exact ih


-- Rather than making a repr instance for GossipState, its easier to assume s is decidable and use repr.
def showState (s : GossipState n) [DecidableRel s] : Lean.Format :=
    repr (fun i j => if s i j then "True " else "False")


-- Prop: All gossip that is known in s1 is also known in s2.
def moreGossip (s1 s2 : GossipState n) : Prop := ∀ a b : Fin n, (s1 a b) → (s2 a b)

-- Adds an agent to a state, that knows only their own secret.
def addAgent (s : GossipState n) : GossipState (n.succ) :=
  λ a b => Fin.lastCases (b == Fin.last n)
                         (fun i => Fin.lastCases (false)
                                                 (fun b => s i b)
                                                b) a

-- Same call contents, but different type to match the larger state.
def expandCall {n : ℕ} (c : Call n) : Call (Nat.succ n) :=
  match c with
    | (i, j) => (i.castSucc, j.castSucc)

-- Expands a list of calls to the larger state.
def expandCalls {n : ℕ} (cs : List (Call n)) : List (Call (Nat.succ n)) :=
  cs.map expandCall

-- Two states are identical if they contain the same gossip.
def stateEquivalence : GossipState n → GossipState n → Prop :=
  λ s1 s2 => ∀ a b, s1 a b ↔ s2 a b

-- The call sequence contains contain agent a.
def contains (σ : List (Call n)) (a : Fin (n)) : Bool :=
  σ.any (λ c' => c'.1 = a ∨ c'.2 = a)


-- Being called by an expert means becoming an expert.
lemma expertMakesExpert {s : GossipState n} {i j : Fin n} :
  isExpert s i → isExpert (makeCall s (i, j)) j := by
  unfold isExpert
  intro h j_1
  simp [makeCall]
  simp_all only [or_true, ite_self]


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
lemma makeCall_increases_gossip (s1 s2 : GossipState n) (c : Call n) :
  moreGossip s1 s2 → moreGossip (makeCall s1 c) (makeCall s2 c) := by
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
lemma makeCallsIncreasesGossip (s1 s2 : GossipState n) (cs : List (Call n)) :
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
lemma makeCallMakesGossip (s : GossipState n) (c : Call n) :
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
lemma callsIncreaseGossip (s : GossipState n) (cs : List (Call n)) :
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
        apply makeCallMakesGossip -- uses the previous lemma for a single call.
      simp_all [moreGossip]


-- An expert in the old state knows all but the new agent's secret if an agent is added.
lemma addAgentExpertOld {s : GossipState n} {i : Fin n} :
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


-- We can replace addAgent with initialState (n + 1) in the following lemma n ≥ 4.
lemma addAgentEqualsSucc {n : ℕ} :
  addAgent (initialState n) = (initialState (Nat.succ n)) := by
  induction n
  case zero =>
    simp [addAgent, initialState]
    unfold initialState
    unfold addAgent
    simp
    unfold Fin.last
    simp_all
    funext x x_1
    simp_all
    constructor
    case mp =>
      intro _
      ext
      simp_all
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


-- addAgent (initialState n) is replacable with initialState (n + 1) in the following lemma.
lemma singleMakeCalls {n : Nat} (initial_call : Call (n + 1)) (expandedSeq : List (Call (n + 1))) :
  makeCall (makeCalls (makeCall (addAgent (initialState n)) initial_call) expandedSeq) initial_call =
  makeCalls (initialState (n + 1)) ([initial_call] ++ expandedSeq ++ [initial_call]) := by
  rw [← makeCalls_cons, addAgentEqualsSucc, makeCalls_snoc]
  simp_all only [List.singleton_append]


-- Adding an agent before a call is equivalent to adding an agent after the call if the call doesn't involve the new agent.
lemma addAgentEquivCall {n : Nat} (c : Call n) (i : Fin (Nat.succ
n)) :
    (c.1.castSucc ≠ i) ∧ (c.2.castSucc ≠ i) →
      makeCall (addAgent (initialState n)) (expandCall c)
    = addAgent (makeCall (initialState n) c) := by
  rintro ⟨h1, h2⟩
  simp_all only [expandCall, ne_eq, not_false_eq_true]
  rcases c with ⟨a, b⟩
  unfold makeCall initialState addAgent
  simp only [beq_iff_eq, Fin.lastCases_castSucc]
  funext x x_1
  split_ifs
  all_goals simp_all
  · simp_all [Fin.lastCases, Fin.reverseInduction]
    aesop
  · simp_all [Fin.lastCases, Fin.reverseInduction]
    aesop
  · simp_all [Fin.lastCases, Fin.reverseInduction]
    aesop


-- Lemma to prove the negation of contains for the tail from the whole list.
lemma notContainedTail {n : Nat} {tail : List (Call n)} {a b : Fin n} (h : ¬ contains (expandCalls ((a, b) :: tail)) (Fin.last n)) :
  ¬ contains (expandCalls tail) (Fin.last n) :=
  fun h1 =>
    have h2 : contains (expandCalls ((a, b) :: tail)) (Fin.last n) := by
      simp [contains, expandCalls, List.any, (· ++ ·)] at *
      exact Or.inr h1
    h h2


-- Lemma stating that a single call Fin n x Fin n can never contain Fin.last n.
lemma singleCantContainLast {n : Nat} (c : Call n) :
  ¬ ( (expandCall c).1 = (Fin.last n) ∨ (expandCall c).1 = (Fin.last n) ) := by
  simp [expandCalls, expandCall, contains]
  have := Fin.castSucc_lt_last c.1
  have := Fin.castSucc_lt_last c.2
  aesop


-- Lemma stating that a call sequence List (Fin n x Fin n) can never contain Fin.last n.
lemma cantContainLast {n : Nat} (σ : List (Call n)) :
  ¬ contains (expandCalls σ) (Fin.last n) := by
  simp [expandCalls, expandCall, contains]
  intro x x_in
  have := Fin.castSucc_lt_last x.1
  have := Fin.castSucc_lt_last x.2
  aesop


-- addAgent and makeCall commute if the call doesn't contain the new agent.
lemma addAgentMakeCallCommute {n : Nat} (c : Call n) (someState : GossipState n):
      makeCall (addAgent someState) (expandCall c)
    = addAgent (makeCall someState c) := by
  have := singleCantContainLast c
  apply funext
  intro x
  apply funext
  intro y
  rcases c with ⟨a,b⟩
  simp [makeCall, expandCall]
  cases em (x = Fin.castSucc a) <;> cases em (x = Fin.castSucc b)
  all_goals
    simp_all [addAgent]
  all_goals
    cases em (y = Fin.last n)
  all_goals
    simp_all [makeCall, Fin.lastCases, Fin.reverseInduction]
  · have : b = a := by
      rw [← Fin.castSucc_inj]
      rename_i h _ _
      exact h
    simp_all
  · aesop
  · aesop


-- addAgent and makeCalls commute if the call sequence doesn't contain the new agent.
lemma addAgentMakeCallsCommute {n : Nat} (σ : List (Call n)) (someState : GossipState n):
      makeCalls (addAgent someState) (expandCalls σ)
    = addAgent (makeCalls someState σ) := by
  induction σ generalizing someState
  case nil =>
    simp_all [makeCalls, expandCalls]
  case cons c σ IH =>
    rcases c with ⟨a,b⟩
    specialize IH (makeCall someState (a, b))
    simp_all [expandCalls, expandCall, addAgent, makeCalls]
    rw [← IH]
    clear IH
    have equiv : makeCall (addAgent someState) (Fin.castSucc a, Fin.castSucc b) = addAgent (makeCall someState (a, b)) :=
      addAgentMakeCallCommute (a,b) _ -- Uses the lemma for a single call.
    rw [equiv]


-- If two states that both have makeCall (initialState) (a, b) are equivalent, then the outer states without the inner call are equivalent.
lemma makeCallEquivalence {n : Nat} (a b : Fin n) (tail : List (Call n)) :
      addAgent (makeCalls (initialState n) tail)
    = makeCalls (addAgent (initialState n)) (expandCalls tail)
    →
      addAgent (makeCalls (makeCall (initialState n) (a, b)) tail)
    = makeCalls (addAgent (makeCall (initialState n) (a, b))) (expandCalls tail) := by
  intro _
  have := addAgentMakeCallsCommute tail
  simp_all


-- The addAgent can be swapped with the makeCalls if the call sequence doesn't contain the last agent.
lemma addAgentCanSwap {n : Nat} (σ : List (Call n)) : ¬ contains (expandCalls σ) (Fin.last n) →
  addAgent (makeCalls (initialState n) σ) = makeCalls (addAgent (initialState n)) (expandCalls σ) := by
  intro h
  induction σ
  case nil =>
    simp [makeCalls, expandCalls]
  case cons =>
    rename_i head tail tail_ih
    rw [makeCalls_cons]
    cases head
    rename_i a b
    if a_eq : a = Fin.last n then
      simp [contains, expandCalls, expandCall] at h
      aesop
    else
      if b_eq : b = Fin.last n then
        simp [contains, expandCalls, expandCall] at h
        aesop
      else
        simp [expandCalls]
        rw [makeCalls_cons]
        rw [addAgentEquivCall (a, b) (Fin.last n)]
        · have replacement : List.map expandCall tail = expandCalls tail := by
            simp [expandCalls]
          rw [replacement]
          rw [makeCallEquivalence a b tail]
          have not_contains : ¬ contains (expandCalls tail) (Fin.last n) := by
            apply notContainedTail h
          aesop
        · constructor
          · simp
            aesop
          · simp
            aesop


-- We can move the addAgent one layer deeper since the call sequence doesn't contain the last agent.
lemma addAgentReplaceable {n : Nat} (σ : List (Call n)) : (makeCalls (addAgent (initialState n)) (expandCalls σ)) = (addAgent (makeCalls (initialState n) σ)) := by
  have old_sequence : ¬ contains (expandCalls σ) (Fin.last n) := by
    apply cantContainLast
  rw [addAgentCanSwap σ old_sequence]


-- Given that only a knows a and b, then we can show that all agents that learn a also learn b.
lemma twoSecretsSuccSingle {n : Nat} (s : GossipState (Nat.succ (n + 4))) (a b : Fin (Nat.succ (n + 4))) (seq : List (Call (Nat.succ (n + 4))))
  (a_def : a = 0)
  (b_def : b = Fin.last (n + 4))
  (only_ab_know_ab : ∀ (i : Fin (Nat.succ (n + 4))), (i ≠ a ∧ i ≠ b) → ¬ s i a ∧ ¬ s i b)
  (a_knows_b : s a b)
  (b_knows_a : s b a)
  (fin_succ_knows_own : s b b)
  :
  (∀ k, (makeCalls s seq) k a → (makeCalls s seq) k b) := by
  induction seq using List.list_reverse_induction
  case base =>
    intro k k_knows_a
    subst_eqs
    simp [makeCalls] at *
    cases em (k = 0) <;> cases em (k = Fin.last (n+4))
    all_goals
      simp_all
  case ind seq theCall IH =>
    intro k k_knows_a
    rcases theCall with ⟨c1,c2⟩
    simp [makeCalls] at *
    simp [makeCall] at k_knows_a
    cases em (c1 = a) <;> cases em (c2 = a)
    -- c1 = a and c2 = a
    · rename_i c1_a c2_a
      rw [c1_a]
      rw [c2_a]
      simp [makeCall]
      split
      · rename_i k_a
        right
        apply callsIncreaseGossip
        exact a_knows_b
      · rename_i k_not_a
        split at k_knows_a
        · cases k_knows_a
          · rename_i h
            apply IH k h
          · rename_i h k_c1
            aesop
        · have k_not_c2 : k ≠ c2 := by
            aesop
          rw [if_neg k_not_c2] at k_knows_a
          apply IH k k_knows_a
    -- c1 = a and c2 ≠ a
    · rename_i c1_a c2_not_a
      simp [makeCall]
      split
      · rename_i k_c1
        left
        rw [k_c1]
        rw [c1_a]
        apply callsIncreaseGossip
        exact a_knows_b
      · rename_i k_not_c1
        split at k_knows_a
        · rename_i k_c1
          contradiction
        · split
          · rename_i k_c2
            rw [if_pos k_c2] at k_knows_a
            cases k_knows_a
            · rename_i h
              left
              apply IH k h
            · rename_i h
              right
              rw [c1_a]
              apply callsIncreaseGossip
              exact a_knows_b
          ·  aesop
    -- c1 ≠ a and c2 = a
    · rename_i c1_not_a c2_a
      simp [makeCall]
      split
      · rename_i k_c1
        right
        rw [c2_a]
        apply callsIncreaseGossip
        exact a_knows_b
      · rename_i k_not_c1
        split
        · rename_i k_c2
          rw [k_c2]
          rw [c2_a]
          left
          apply callsIncreaseGossip
          exact a_knows_b
        · rename_i k_not_c2
          rw [if_neg k_not_c1] at k_knows_a
          rw [if_neg k_not_c2] at k_knows_a
          apply IH k k_knows_a
    -- c1 ≠ a and c2 ≠ a
    · rename_i c1_not_a c2_not_a
      simp [makeCall]
      split
      · rename_i k_c1
        rw [if_pos k_c1] at k_knows_a
        cases k_knows_a
        · rename_i h
          left
          apply IH k h
        · rename_i h
          aesop
      · rename_i k_not_c1
        · split
          · rename_i k_c2
            rw [if_pos k_c2] at k_knows_a
            rw [if_neg k_not_c1] at k_knows_a
            · rename_i h
              cases k_knows_a
              · rename_i h
                left
                apply IH k h
              · aesop
          · rename_i k_not_c2
            rw [if_neg k_not_c1] at k_knows_a
            rw [if_neg k_not_c2] at k_knows_a
            apply IH k k_knows_a


-- Given that only agent a knows a and b, and some sequence makes everyone else learn a, then everyone else also learns b.
lemma twoSecretsSucc {n : Nat} (s : GossipState (Nat.succ (n + 4))) (a b : Fin (Nat.succ (n + 4))) (seq : List (Call (Nat.succ (n + 4))))
  (a_def : a = 0)
  (b_def : b = Fin.last (n + 4))
  (only_ab_know_ab : ∀ (i : Fin (Nat.succ (n + 4))), (i ≠ a ∧ i ≠ b) → ¬ s i a ∧ ¬ s i b)
  (a_knows_b : s a b)
  (b_knows_a : s b a)
  (all_learn_a : ∀ j, (makeCalls s seq) j a)
  (fin_succ_knows_own : s b b)
  :
  (∀ k, (makeCalls s seq) k b) := by
  intro k
  apply twoSecretsSuccSingle s a b seq a_def b_def only_ab_know_ab a_knows_b b_knows_a fin_succ_knows_own
  apply all_learn_a


-- Definitions to avoid repetition.
def zero_fin : (Fin (Nat.succ (n + 4))) := 0
def succ_fin : (Fin (Nat.succ (n + 4))) := Fin.last (n + 4)
def initial_call : Call (Nat.succ (k + 4)) := (zero_fin, succ_fin)


-- Shows that the first agent learns all old secrets.
lemma lemma_1 {k : Nat} (seq : List (Call (k + 4))) (IH : allExpert (makeCalls (initialState (k + 4)) seq)) :
  ∀ i : Fin (Nat.succ (k + 4)), i ≠ Fin.last (k + 4) → makeCalls (makeCall (addAgent (initialState (k + 4))) (zero_fin, succ_fin)) (expandCalls seq) zero_fin i := by
  unfold allExpert at IH
  let expandedSeq := expandCalls seq
  let new_state := makeCall (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) expandedSeq) initial_call
  let calls_without_final_call := [initial_call] ++ expandedSeq
  let temp_state := makeCalls (addAgent (initialState (k + 4))) calls_without_final_call

  have single_calls : new_state = makeCalls (initialState (Nat.succ (k + 4))) ([initial_call] ++ expandedSeq ++ [initial_call]) := by
    simp [new_state]
    apply singleMakeCalls

  have h : ∀ i, i ≠ succ_fin → makeCalls (addAgent (initialState (k + 4))) expandedSeq zero_fin i := by
    simp_all only [expandedSeq, isExpert]
    let zero_fin_old := 0
    have h' : isExpert (makeCalls (initialState (k + 4)) seq) zero_fin_old := by
      apply IH

    rw [addAgentExpertOld] at h'
    simp [succ_fin]
    have replacement := addAgentReplaceable seq
    simp [stateEquivalence] at replacement

    apply Fin.lastCases
    · intro a
      simp_all only [le_add_iff_nonneg_left, zero_le, Nat.cast_zero]
      aesop
    · intro i _
      simp_all only [Nat.cast_zero, Fin.castSucc_zero, zero_fin_old, initial_call, zero_fin]


  -- New_state contains more gossip than temp_state.
  have h' : moreGossip (makeCalls (addAgent (initialState (k + 4))) expandedSeq) temp_state := by
    simp [temp_state, calls_without_final_call, expandedSeq]
    rw [addAgentEqualsSucc, makeCalls_cons]
    apply makeCallsIncreasesGossip
    unfold moreGossip
    intro a b
    apply makeCallMakesGossip

  intro i a
  simp_all only [ne_eq, new_state, initial_call, zero_fin, succ_fin, expandedSeq]
  apply h'
  aesop


-- Shows that the first agent learns the new agent's secret.
lemma lemma_2 {k : Nat} (seq : List (Call (k + 4))) :
  (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) (expandCalls seq)) zero_fin succ_fin := by
  let new_state := makeCall (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) (expandCalls seq)) initial_call
  have l : moreGossip (makeCall (addAgent (initialState (k + 4))) initial_call) (makeCalls ((makeCall (addAgent (initialState (k + 4))) initial_call)) (expandCalls seq)) := by
    apply callsIncreaseGossip
  apply l
  simp [initial_call, makeCall]
  right
  simp [addAgent, initialState]
  simp_all only [Fin.lastCases_last, new_state, zero_fin, succ_fin]


-- Combining lemma_1 and lemma_2 to show that the first agent is an expert.
lemma lemma_3 {k : Nat} (seq : List (Call (k + 4))) (IH : allExpert (makeCalls (initialState (k + 4)) seq)) :
  isExpert (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) (expandCalls seq)) zero_fin := by
  unfold isExpert
  let calls_without_final_call := [initial_call] ++ (expandCalls seq)
  let temp_state := makeCalls (addAgent (initialState (k + 4))) calls_without_final_call
  intro j
  have h1 : j ≠ succ_fin → temp_state zero_fin j := by
    exact lemma_1 seq IH j
  have h2 : j = succ_fin → temp_state zero_fin j := by
    intro h
    rw [h]
    exact lemma_2 seq
  by_cases (j = succ_fin)
  · rename_i l
    simp [temp_state] at h2
    exact h2 l
  · rename_i l
    simp [temp_state] at h1
    exact h1 l


-- Main lemma for the inductive step.
lemma inductiveCase (k : Nat) (seq : List (Call (k + 4))):
    allExpert (makeCalls (initialState (k + 4)) seq) →
    ∃ seq', seq'.length = 2 + seq.length ∧ allExpert (makeCalls (initialState (Nat.succ k + 4)) seq') := by
  intro IH
  let expandedSeq := expandCalls seq
  let zero_fin : Fin (Nat.succ (k + 4)) := 0
  let succ_fin : Fin (Nat.succ (k + 4)) := Fin.last (k + 4)
  let initial_call : Call (Nat.succ (k + 4)) := (zero_fin, succ_fin)
  let new_state := makeCall (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) expandedSeq) initial_call
  let calls_without_final_call := [initial_call] ++ expandedSeq
  let temp_state := makeCalls (addAgent (initialState (k + 4))) calls_without_final_call

  -- We can rewrite new_state so it contains a single call sequence.
  have single_calls : new_state = makeCalls (initialState (Nat.succ (k + 4))) ([initial_call] ++ expandedSeq ++ [initial_call]) := by
    simp [new_state]
    apply singleMakeCalls

  -- All but the last agent learn the secret of the new agent using all but the final call.
  have milestone_1_test : ∀ i, i ≠ succ_fin → temp_state zero_fin i := by
    exact lemma_1 seq IH

  -- The first agent learns the secret of the new agent.
  have milestone_2 : temp_state zero_fin succ_fin := by
    apply lemma_2 seq

  -- Thus the first agent is an expert.
  have milestone_3 : isExpert temp_state zero_fin := by
    apply lemma_3 seq IH

  -- Putting milestone_1 and milestone_2 together, we get that all but the last agents are experts
  have milestone_4 : ∀ i, i ≠ succ_fin → isExpert new_state i := by
    -- The goal is true for temp_state.
    have subgoal_1 : ∀ i, i ≠ succ_fin → ∀ j, temp_state i j := by
      intro i h
      simp [temp_state, calls_without_final_call, expandedSeq]
      simp [allExpert] at IH

      -- All agents of the old state are experts in the old state.
      have h' : isExpert (makeCalls (initialState (k + 4)) seq) i := by
        apply IH

      -- Need to introduce new agent's secret.
      rw [addAgentExpertOld] at h'

      -- All old agents know all old secrets in temp_state.
      have subsubgoal1 : ∀ (j : Fin (k + 4)), (makeCalls (addAgent (initialState (k + 4))) (initial_call :: expandCalls seq)) i (Fin.castSucc j) := by

        -- Its true for this state.
        have weaker_state : ∀ (j : Fin (k + 4)), makeCalls (addAgent (initialState (k + 4))) (expandCalls seq) i.castSucc j.castSucc := by

          -- For all fin (k + 4), they know all but the last secret.
          have know_all_but_last : ∀ (i : Fin (k + 4)), ∀ (j : Fin (k + 4)), makeCalls (addAgent (initialState (k + 4))) (expandCalls seq) i.castSucc j.castSucc := by
            intro i j
            rw [addAgentReplaceable]
            simp [addAgent]
            aesop

          -- Turn the type into Fin (Nat.succ (k + 4)) with i ≠ Fin.last (k + 4).
          have type_cast : ∀ (i : Fin (Nat.succ (k + 4))), i ≠ Fin.last (k + 4) → ∀ (j : Fin (k + 4)), makeCalls (addAgent (initialState (k + 4))) (expandCalls seq) i j.castSucc := by
            intro i i_neq_last
            cases i using Fin.lastCases
            case last => exfalso; tauto
            case cast i =>
              intro j
              exact know_all_but_last i j
          aesop

        -- This state is stronger.
        have stronger_state : moreGossip (makeCalls (addAgent (initialState (k + 4))) (expandCalls seq)) (makeCalls (addAgent (initialState (k + 4))) (initial_call :: expandCalls seq)) := by
          apply makeCallsIncreasesGossip
          apply makeCallMakesGossip

        aesop

      -- All i learn the secret of the new agent as well.
      have subsubgoal2 : makeCalls (addAgent (initialState (k + 4))) (initial_call :: expandCalls seq) (i.castSucc) succ_fin := by
        -- prepare for the lemma.
        have agent_0_knows_both : temp_state zero_fin succ_fin ∧ temp_state zero_fin zero_fin := by
          constructor
          · apply milestone_3
          · apply milestone_3
        clear milestone_3

        -- All agents get to learn the new agent's secret.
        have all_know_new_secret : makeCalls (addAgent (initialState (k + 4))) (initial_call :: expandCalls seq) i.castSucc succ_fin := by
          have fin_succ_knows_own : makeCall (addAgent (initialState (k + 4))) initial_call succ_fin succ_fin := by
            simp only [makeCall, addAgent, beq_self_eq_true, or_self, ↓reduceIte]
            split
            · have less : 1 < Fin.last (k + 4) := by
                apply Fin.one_lt_last
              aesop
            · simp [Fin.lastCases, Fin.reverseInduction]

          apply twoSecretsSucc (makeCall (addAgent (initialState (k + 4))) initial_call) zero_fin succ_fin (expandCalls seq) (by aesop) (by unfold_let succ_fin; rfl)
          case only_ab_know_ab =>
            intro i h
            constructor
            · cases i using Fin.lastCases
              case last =>
                aesop
              case cast _ i =>
                simp [initial_call, makeCall, addAgent, initialState]
                aesop
            · cases i using Fin.lastCases
              case last =>
                aesop
              case cast _ i =>
                simp [initial_call, makeCall, addAgent, initialState]
                aesop
          case a_knows_b =>
            simp [makeCall]
            right
            simp [addAgent, initialState]
            aesop
          case b_knows_a =>
            simp [makeCall, zero_fin, succ_fin]
            rw [if_neg]
            · right
              simp [addAgent, initialState, Fin.lastCases, Fin.reverseInduction]
              aesop
            · have less : 1 < Fin.last (k + 4) := by
                apply Fin.one_lt_last
              aesop
          case all_learn_a =>
            have old_agents_learn_a : ∀ (j : Fin (k + 4)), makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) (expandCalls seq) j.castSucc zero_fin := by
              intro j
              have know_all_but_last : ∀ (i : Fin (k + 4)), ∀ (j : Fin (k + 4)), makeCalls (addAgent (initialState (k + 4))) (expandCalls seq) i.castSucc j.castSucc := by
                intro i j
                rw [addAgentReplaceable]
                simp [addAgent]
                aesop
              have weaker : moreGossip (makeCalls (addAgent (initialState (k + 4))) (expandCalls seq)) (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) (expandCalls seq)) := by
                apply makeCallsIncreasesGossip
                apply makeCallMakesGossip
              apply weaker
              exact know_all_but_last j zero_fin

            have new_agent_learns_a : makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) (expandCalls seq) succ_fin zero_fin := by
              have weaker : moreGossip (makeCall (addAgent (initialState (k + 4))) initial_call) (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) (expandCalls seq)) := by
                apply callsIncreaseGossip

              apply weaker
              simp_all only [makeCall, addAgent, initialState]
              rw [if_neg]
              · simp [succ_fin, zero_fin]
                right
                simp [Fin.lastCases, Fin.reverseInduction]
                aesop
              · have less : 1 < Fin.last (k + 4) := by
                  apply Fin.one_lt_last
                aesop

            intro j
            cases j using Fin.lastCases
            case last => exact new_agent_learns_a
            case cast j =>
              rw [makeCalls_cons] at subsubgoal1
              exact old_agents_learn_a j
          case fin_succ_knows_own =>
            exact fin_succ_knows_own

        cases i using Fin.lastCases
        case last => exfalso; tauto
        case cast i =>
          exact all_know_new_secret


      -- Putting them together in the right format.
      have final : ∀ (j : Fin (Nat.succ (k + 4))), temp_state i j := by
        intro j

        -- All old agents know the new agent's secret.
        have final_secret : temp_state (i.castSucc) succ_fin := by
          aesop

        -- All old agents know all old secrets in the new state.
        have other_secrets : ∀ (q : Fin (k + 4)), temp_state i (q.castSucc) := by
          aesop

        -- Rewritten to ensure the type is correct.
        have other_secrets_rewritten : ∀ (q : Fin (Nat.succ (k + 4))), temp_state i q := by
          intro q
          cases q using Fin.lastCases <;> cases i using Fin.lastCases
          all_goals simp_all

        simp [succ_fin] at final_secret
        aesop
      aesop

    simp [new_state, isExpert]

    -- The goal is true for temp_state, which is weaker than new_state, so it's true for new_state.
    have subgoal_2 : moreGossip temp_state new_state := by
      simp [temp_state, new_state, calls_without_final_call, expandedSeq]
      apply makeCallMakesGossip

    intro i a j
    simp_all only [ne_eq, new_state]
    apply subgoal_2
    simp_all only [not_false_eq_true]



  -- putting milestone_3 and milestone_4 together, we get that everyone is an expert.
  have milestone_5 : allExpert new_state := by

    have new_becomes_expert : isExpert new_state succ_fin := by
      have h : isExpert temp_state zero_fin := by
        unfold isExpert
        intro j
        simp_all only [temp_state, calls_without_final_call]
        simp_all only [List.singleton_append]
        apply milestone_3

      have state_equiv : new_state = makeCall temp_state initial_call := by
        rw [single_calls]
        simp [temp_state, calls_without_final_call, expandedSeq]
        repeat rw [makeCalls_cons]
        rw [makeCalls_snoc, addAgentEqualsSucc]

      rw [state_equiv]
      apply expertMakesExpert
      exact h

    unfold allExpert
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


-- Main theorem for the sufficiency proof that there exists a sequence of calls that makes everyone an expert for n ≥ 4.
theorem sufficiency (n : Nat) : (n ≥ 4) → ∃ (seq : List (Call n)), seq.length = (2 * n - 4) ∧ allExpert (makeCalls (initialState n) seq) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | 2 => by simp
  | 3 => by simp
  | (m + 4) =>  by -- we perform induction on m = n - 4 so the base case is m = 0, i.e. n = 4
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
                  exact inductiveCase k seq claim.right
