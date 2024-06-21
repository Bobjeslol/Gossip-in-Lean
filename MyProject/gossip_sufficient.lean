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
    | (i, j) => (i.castSucc, j.castSucc)

-- Expands a list of calls to the larger state.
def expandCalls {n : ℕ} (cs : List (Call n)) : List (Call (Nat.succ n)) :=
  cs.map expandCall

-- Two states are identical if they contain the same gossip.
def stateEquivalence : GossipState n → GossipState n → Prop :=
  λ s1 s2 => ∀ a b, s1 a b ↔ s2 a b


-- An agent always knows their own secret.
lemma own_secret (s : GossipState n) (i : Fin n) : s i i := by
  sorry


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
lemma addAgent_equiv_call {n : Nat} (c : Call n) (i : Fin (Nat.succ n)) :
  (c.1.castSucc ≠ i) ∧ (c.2.castSucc ≠ i) → makeCall (addAgent (initialState n)) (expandCall c) = addAgent (makeCall (initialState n) c) := by
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
  -- aesop (config := {maxRuleApplications := 10000})
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


-- The call sequence contains contain agent a
def contains (σ : List (Call n)) (a : Fin (n)) : Bool :=
  σ.any (λ c' => c'.1 = a ∨ c'.2 = a)


-- Lemma to prove the negation of contains for the tail from the whole list
lemma not_contains_in_tail {n : Nat} {tail : List (Call n)} {a b : Fin n} (h : ¬ contains (expandCalls ((a, b) :: tail)) (Fin.last n)) :
  ¬ contains (expandCalls tail) (Fin.last n) :=
  fun h1 =>
    have h2 : contains (expandCalls ((a, b) :: tail)) (Fin.last n) := by
      simp [contains, expandCalls, List.any, (· ++ ·)] at *
      exact Or.inr h1
    h h2


-- Lemma stating that a single call Fin n x Fin n can never contain Fin.last n
lemma single_cant_contain_last {n : Nat} (c : Call n) :
  ¬ ( (expandCall c).1 = (Fin.last n) ∨ (expandCall c).1 = (Fin.last n) ) := by
  simp [expandCalls, expandCall, contains]
  have := Fin.castSucc_lt_last c.1
  have := Fin.castSucc_lt_last c.2
  aesop


-- Lemma stating that a call sequence List (Fin n x Fin n) can never contain Fin.last n
lemma cant_contain_last {n : Nat} (σ : List (Call n)) :
  ¬ contains (expandCalls σ) (Fin.last n) := by
  simp [expandCalls, expandCall, contains]
  intro x x_in
  have := Fin.castSucc_lt_last x.1
  have := Fin.castSucc_lt_last x.2
  aesop


-- addAgent and makeCall commute if the call doesn't contain the new agent
lemma addAgent_makeCall_commute {n : Nat} (c : Call n) (someState : GossipState n):
      makeCall (addAgent someState) (expandCall c)
    = addAgent (makeCall someState c) := by
  have := single_cant_contain_last c
  apply funext
  intro x
  apply funext
  intro y
  rcases c with ⟨a,b⟩
  simp [makeCall, expandCall]
  -- Now the goal is depending on whether x=a, whether x=b
  -- So let's split cases according to that.
  cases em (x = Fin.castSucc a) <;> cases em (x = Fin.castSucc b)
  -- Now we have 4 goals...
  all_goals
    simp_all [addAgent]
  -- The goals now depend on whether y=Fin.last, so let's split cases on that.
  all_goals
    cases em (y = Fin.last n)
  -- Now we have 8 goals...
  all_goals
    simp_all [makeCall, Fin.lastCases, Fin.reverseInduction]
  -- Nowe we have 3 goals left...
  · have : b = a := by
      rw [← Fin.castSucc_inj]
      rename_i h _ _
      exact h
    simp_all
  · aesop
  · aesop

-- addAgent and makeCalls commute if the call sequence doesn't contain the new agent
lemma addAgent_makeCalls_commute {n : Nat} (σ : List (Call n)) (someState : GossipState n):
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
    have : makeCall (addAgent someState) (Fin.castSucc a, Fin.castSucc b) = addAgent (makeCall someState (a, b)) := addAgent_makeCall_commute (a,b) _
    rw [this]


-- If two states that both have makeCall (initialState) (a, b) are equivalent, then the outer states without the inner call are equivalent.
lemma makeCall_equivalence {n : Nat} (a b : Fin n) (tail : List (Call n)) :
      addAgent (makeCalls (initialState n) tail)
    = makeCalls (addAgent (initialState n)) (expandCalls tail)
    →
      addAgent (makeCalls (makeCall (initialState n) (a, b)) tail)
    = makeCalls (addAgent (makeCall (initialState n) (a, b))) (expandCalls tail) := by
  intro _
  have := addAgent_makeCalls_commute tail
  simp_all


-- The addAgent can be swapped with the makeCalls if the call sequence doesn't contain the last agent
lemma addAgent_can_swap {n : Nat} (σ : List (Call n)) : ¬ contains (expandCalls σ) (Fin.last n) →
  addAgent (makeCalls (initialState n) σ) = makeCalls (addAgent (initialState n)) (expandCalls σ) := by
  intro h
  induction σ
  case nil =>
    simp [makeCalls, expandCalls]
  case cons =>
    rename_i head tail tail_ih
    rw [makeCalls_cons]
    -- unfold makeCall
    cases head
    rename_i a b
    if a_eq : a = Fin.last n then
      simp [contains, expandCalls, expandCall] at h
      aesop?
    else
      if b_eq : b = Fin.last n then
        simp [contains, expandCalls, expandCall] at h
        aesop?
      else
        simp [expandCalls]
        rw [makeCalls_cons]
        rw [addAgent_equiv_call (a, b) (Fin.last n)]
        · have replacement : List.map expandCall tail = expandCalls tail := by
            simp [expandCalls]
          rw [replacement]
          rw [makeCall_equivalence a b tail]
          have not_contains : ¬ contains (expandCalls tail) (Fin.last n) := by
            apply not_contains_in_tail h
          aesop?
        · constructor
          · simp
            aesop?
          · simp
            aesop?


-- We can move the addAgent one layer deeper if σ has type List (Call n) (and not List (Call (n + 1))
lemma addAgent_replacable {n : Nat} (σ : List (Call n)) : stateEquivalence (makeCalls (addAgent (initialState n)) (expandCalls σ)) (addAgent (makeCalls (initialState n) σ)) := by
  -- The old sequence doesn't contain the old agent.
  have old_sequence : ¬ contains (expandCalls σ) (Fin.last n) := by
    apply cant_contain_last
  rw [addAgent_can_swap σ old_sequence]
  simp [stateEquivalence]


-- Given that agent a only knows secret b, and a call (a, c) makes some other agent c learn secret a, then the call must also make c learn b, provided c ≠ a and a ≠ b.
lemma single_call_specific {n : Nat} (s : GossipState (Nat.succ n)) (a b c : Fin (Nat.succ n)) : c ≠ a → a ≠ b → s a b → (makeCall s (a, c)) c a → (makeCall s (a, c)) c b := by
  intro h_ca _ h_aca
  simp [makeCall]
  simp_all only [ne_eq, not_false_eq_true]
  rw [if_neg]
  · aesop?
  · rw [not_false_eq_true]
    simp



-- Given that only a knows a and b, then we can show that all agents that learn a also learn b.
lemma two_secrets_succ_single {n : Nat} (s : GossipState (Nat.succ (n + 4))) (a b : Fin (Nat.succ (n + 4))) (seq : List (Call (Nat.succ (n + 4))))
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
        apply calls_increase_gossip
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
        apply calls_increase_gossip
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
              apply calls_increase_gossip
              exact a_knows_b
          ·  aesop
    -- c1 ≠ a and c2 = a
    · rename_i c1_not_a c2_a
      simp [makeCall]
      split
      · rename_i k_c1
        right
        rw [c2_a]
        apply calls_increase_gossip
        exact a_knows_b
      · rename_i k_not_c1
        split
        · rename_i k_c2
          rw [k_c2]
          rw [c2_a]
          left
          apply calls_increase_gossip
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


-- Given that only agent a knows a and b, and some sequence makes everyone else learn a, then everyone else also learns b
lemma two_secrets_succ {n : Nat} (s : GossipState (Nat.succ (n + 4))) (a b : Fin (Nat.succ (n + 4))) (seq : List (Call (Nat.succ (n + 4))))
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
  apply two_secrets_succ_single s a b seq a_def b_def only_ab_know_ab a_knows_b b_knows_a fin_succ_knows_own
  apply all_learn_a


def zero_fin : (Fin (Nat.succ (n + 4))) := 0
def succ_fin : (Fin (Nat.succ (n + 4))) := Fin.last (n + 4)
def initial_call : Call (Nat.succ (k + 4)) := (zero_fin, succ_fin)


lemma lemma_1 {k : Nat} (seq : List (Call (k + 4))) (IH : checkIfEE (makeCalls (initialState (k + 4)) seq)) :
  ∀ i : Fin (Nat.succ (k + 4)), i ≠ Fin.last (k + 4) → makeCalls (makeCall (addAgent (initialState (k + 4))) (zero_fin, succ_fin)) (expandCalls seq) zero_fin i := by
  unfold checkIfEE at IH
  let expandedSeq := expandCalls seq
  let new_state := makeCall (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) expandedSeq) initial_call
  let calls_without_final_call := [initial_call] ++ expandedSeq
  let temp_state := makeCalls (addAgent (initialState (k + 4))) calls_without_final_call

  have single_calls : new_state = makeCalls (initialState (Nat.succ (k + 4))) ([initial_call] ++ expandedSeq ++ [initial_call]) := by
    simp [new_state]
    apply makeCalls_addAgent_initialState_equiv

  have h : ∀ i, i ≠ succ_fin → makeCalls (addAgent (initialState (k + 4))) expandedSeq zero_fin i := by
    simp_all only [expandedSeq, isExpert]
    let zero_fin_old := 0
    have h' : isExpert (makeCalls (initialState (k + 4)) seq) zero_fin_old := by
      apply IH

    rw [addAgent_expert_old] at h'
    simp [succ_fin]
    have replacement := addAgent_replacable seq zero_fin_old -- Still need to do the addAgent_replacable proof
    simp [stateEquivalence] at replacement

    apply Fin.lastCases
    · intro a
      simp_all only [le_add_iff_nonneg_left, zero_le, Nat.cast_zero]
      aesop
    · intro i a
      simp_all only [Nat.cast_zero, Fin.castSucc_zero, zero_fin_old, initial_call, zero_fin]


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
  aesop


lemma lemma_2 {k : Nat} (seq : List (Call (k + 4))) :
  (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) (expandCalls seq)) zero_fin succ_fin := by
  let new_state := makeCall (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) (expandCalls seq)) initial_call
  have l : moreGossip (makeCall (addAgent (initialState (k + 4))) initial_call) (makeCalls ((makeCall (addAgent (initialState (k + 4))) initial_call)) (expandCalls seq)) := by
    apply calls_increase_gossip
  apply l
  simp [initial_call, makeCall]
  right
  simp [addAgent, initialState]
  simp_all only [Fin.lastCases_last, new_state, zero_fin, succ_fin]


lemma lemma_3 {k : Nat} (seq : List (Call (k + 4))) (IH : checkIfEE (makeCalls (initialState (k + 4)) seq)) :
  isExpert (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) (expandCalls seq)) zero_fin := by
  unfold isExpert
  let calls_without_final_call := [initial_call] ++ (expandCalls seq)
  let temp_state := makeCalls (addAgent (initialState (k + 4))) calls_without_final_call
  -- simp [succ_fin] at lemma_2
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

lemma lemma_4_subgoal_1 {k : Nat} (seq : List (Call (k + 4))) (IH : checkIfEE (makeCalls (initialState (k + 4)) seq)) :
  ∀ i, i ≠ succ_fin → ∀ j, (makeCalls (makeCall (addAgent (initialState (k + 4))) (0, Fin.last (k + 4))) (expandCalls seq)) i j := by
  let zero_fin : (Fin (Nat.succ (n + 4))) := 0
  let succ_fin : (Fin (Nat.succ (n + 4))) := Fin.last (n + 4)
  let initial_call : Call (Nat.succ (k + 4)) := (zero_fin, succ_fin)
  let expandedSeq := expandCalls seq
  let new_state := makeCall (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) expandedSeq) initial_call
  let calls_without_final_call := [initial_call] ++ expandedSeq
  let temp_state := makeCalls (addAgent (initialState (k + 4))) calls_without_final_call

  have milestone_1 : ∀ (i : Fin (Nat.succ (k + 4))), i ≠ succ_fin → temp_state zero_fin i := by
    sorry
  have milestone_2 : temp_state zero_fin succ_fin := by
    sorry
  have milestone_3 : isExpert temp_state zero_fin := by
    sorry

  intro i h
  -- rw [← makeCalls_cons]
  -- simp [temp_state, calls_without_final_call, expandedSeq]
  simp [checkIfEE] at IH

  -- All agents of the old state are experts in the old state.
  have h' : isExpert (makeCalls (initialState (k + 4)) seq) i := by
    apply IH

  -- Need to introduce new agent's secret.
  rw [addAgent_expert_old] at h'

  -- We can rewrite the addAgent one layer deeper and add the initial call without losing gossip.
  -- All old agents know all old secrets in the new state
  have h'' : ∀ (j : Fin (k + 4)), (makeCalls (addAgent (initialState (k + 4))) (initial_call :: expandCalls seq)) i (Fin.castSucc j) := by

    -- Its true for this state
    have weaker_state : ∀ (j : Fin (k + 4)), makeCalls (addAgent (initialState (k + 4))) (expandCalls seq) i.castSucc j.castSucc := by

      -- For all fin (k + 4), they know all but the last secret
      have know_all_but_last : ∀ (i : Fin (k + 4)), ∀ (j : Fin (k + 4)), makeCalls (addAgent (initialState (k + 4))) (expandCalls seq) i.castSucc j.castSucc := by
        intro i j
        rw [addAgent_replacable]
        simp [addAgent]
        aesop

      -- This is required, and similar, but not quite the same. How to transform? Shouldnt be too hard
      -- For all Fin (Nat.succ (k + 4)) where i ≠ Fin.last (k + 4), they know all but the last secret
      have type_cast : ∀ (i : Fin (Nat.succ (k + 4))), i ≠ Fin.last (k + 4) → ∀ (j : Fin (k + 4)), makeCalls (addAgent (initialState (k + 4))) (expandCalls seq) i j.castSucc := by
        intro i i_neq_last
        cases i using Fin.lastCases
        case last => exfalso; tauto
        case cast i =>
          intro j
          exact know_all_but_last i j
      aesop

    -- This state is stronger
    have stronger_state : moreGossip (makeCalls (addAgent (initialState (k + 4))) (expandCalls seq)) (makeCalls (addAgent (initialState (k + 4))) (initial_call :: expandCalls seq)) := by
      apply makeCalls_increases_gossip
      apply makeCall_makes_gossip

    aesop

  -- All i learn the secret of the new agent as well.
  have h''' : makeCalls (addAgent (initialState (k + 4))) (initial_call :: expandCalls seq) (i.castSucc) succ_fin := by
    -- prepare for the lemma.
    have agent_0_knows_both : temp_state zero_fin succ_fin ∧ temp_state zero_fin zero_fin := by
      constructor
      · apply lemma_3 seq IH
      · apply lemma_3 seq IH

    -- All agents get to learn the new agent's secret.
    have all_know_new_secret : makeCalls (addAgent (initialState (k + 4))) (initial_call :: expandCalls seq) i.castSucc succ_fin := by
      have fin_succ_knows_own : makeCall (addAgent (initialState (k + 4))) initial_call succ_fin succ_fin := by
        simp only [makeCall, addAgent, beq_self_eq_true, or_self, ↓reduceIte] -- the state here is very different from the state on line 1126
        split
        · have less : 1 < Fin.last (k + 4) := by
            apply Fin.one_lt_last
          aesop?
          sorry
        · simp [Fin.lastCases, Fin.reverseInduction]
          sorry

      apply two_secrets_succ (makeCall (addAgent (initialState (k + 4))) initial_call) zero_fin succ_fin (expandCalls seq) (by aesop) (by unfold_let succ_fin; rfl) -- not sure how to approach this
      case only_ab_know_ab =>
        intro i h
        constructor
        · cases i using Fin.lastCases
          case last =>
            aesop
          case cast _ i =>
            simp [initial_call, makeCall, addAgent, initialState]
            aesop?
        · cases i using Fin.lastCases
          case last =>
            aesop?
          case cast _ i =>
            simp [initial_call, makeCall, addAgent, initialState]
            aesop?
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
          -- Reusing old have statement that is no longer in scope.
          have know_all_but_last : ∀ (i : Fin (k + 4)), ∀ (j : Fin (k + 4)), makeCalls (addAgent (initialState (k + 4))) (expandCalls seq) i.castSucc j.castSucc := by
            intro i j
            rw [addAgent_replacable]
            simp [addAgent]
            aesop
          have weaker : moreGossip (makeCalls (addAgent (initialState (k + 4))) (expandCalls seq)) (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) (expandCalls seq)) := by
            apply makeCalls_increases_gossip
            apply makeCall_makes_gossip
          apply weaker
          exact know_all_but_last j zero_fin

        have new_agent_learns_a : makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) (expandCalls seq) succ_fin zero_fin := by
          have weaker : moreGossip (makeCall (addAgent (initialState (k + 4))) initial_call) (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) (expandCalls seq)) := by
            apply calls_increase_gossip

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
        case cast foo j =>
          rw [makeCalls_cons] at h''
          exact old_agents_learn_a j
      case fin_succ_knows_own =>
        exact fin_succ_knows_own

    -- Type mismatch, need to fix.
    cases i using Fin.lastCases
    case last => exfalso; tauto
    case cast foo i =>
      exact all_know_new_secret


  -- Putting them together in the right format.
  have final : ∀ (j : Fin (Nat.succ (k + 4))), temp_state i j := by
    intro j
    -- all old agents know the new agent's secret
    have final_secret : temp_state (i.castSucc) succ_fin := by
      aesop

    -- all old agents know all old secrets in the new state
    have other_secrets : ∀ (q : Fin (k + 4)), temp_state i (q.castSucc) := by
      aesop

    have other_secrets_rewritten : ∀ (q : Fin (Nat.succ (k + 4))), temp_state i q := by
      intro q
      cases q using Fin.lastCases <;> cases i using Fin.lastCases
      all_goals simp_all

    simp [succ_fin] at final_secret
    aesop
  aesop

  simp [new_state, isExpert]

-- Main lemma for the induction step
lemma inductive_case (k : Nat) (h: Nat.succ k + 4 ≥ 4) (seq : List (Call (k + 4))):
    checkIfEE (makeCalls (initialState (k + 4)) seq) →
    ∃ seq', seq'.length = 2 + seq.length ∧ checkIfEE (makeCalls (initialState (Nat.succ k + 4)) seq') := by
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
    apply makeCalls_addAgent_initialState_equiv

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
      simp [checkIfEE] at IH

      -- All agents of the old state are experts in the old state.
      have h' : isExpert (makeCalls (initialState (k + 4)) seq) i := by
        apply IH

      -- Need to introduce new agent's secret.
      rw [addAgent_expert_old] at h'

      -- We can rewrite the addAgent one layer deeper and add the initial call without losing gossip.
      -- All old agents know all old secrets in the new state
      have h'' : ∀ (j : Fin (k + 4)), (makeCalls (addAgent (initialState (k + 4))) (initial_call :: expandCalls seq)) i (Fin.castSucc j) := by

        -- Its true for this state
        have weaker_state : ∀ (j : Fin (k + 4)), makeCalls (addAgent (initialState (k + 4))) (expandCalls seq) i.castSucc j.castSucc := by

          -- For all fin (k + 4), they know all but the last secret
          have know_all_but_last : ∀ (i : Fin (k + 4)), ∀ (j : Fin (k + 4)), makeCalls (addAgent (initialState (k + 4))) (expandCalls seq) i.castSucc j.castSucc := by
            intro i j
            rw [addAgent_replacable]
            simp [addAgent]
            aesop

          -- This is required, and similar, but not quite the same. How to transform? Shouldnt be too hard
          -- For all Fin (Nat.succ (k + 4)) where i ≠ Fin.last (k + 4), they know all but the last secret
          have type_cast : ∀ (i : Fin (Nat.succ (k + 4))), i ≠ Fin.last (k + 4) → ∀ (j : Fin (k + 4)), makeCalls (addAgent (initialState (k + 4))) (expandCalls seq) i j.castSucc := by
            intro i i_neq_last
            cases i using Fin.lastCases
            case last => exfalso; tauto
            case cast foo i =>
              intro j
              exact know_all_but_last i j
          aesop

        -- This state is stronger
        have stronger_state : moreGossip (makeCalls (addAgent (initialState (k + 4))) (expandCalls seq)) (makeCalls (addAgent (initialState (k + 4))) (initial_call :: expandCalls seq)) := by
          apply makeCalls_increases_gossip
          apply makeCall_makes_gossip

        aesop

      -- All i learn the secret of the new agent as well.
      have h''' : makeCalls (addAgent (initialState (k + 4))) (initial_call :: expandCalls seq) (i.castSucc) succ_fin := by
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
              aesop?
            · simp [Fin.lastCases, Fin.reverseInduction]

          apply two_secrets_succ (makeCall (addAgent (initialState (k + 4))) initial_call) zero_fin succ_fin (expandCalls seq) (by aesop) (by unfold_let succ_fin; rfl)
          case only_ab_know_ab =>
            intro i h
            constructor
            · cases i using Fin.lastCases
              case last =>
                aesop
              case cast _ i =>
                simp [initial_call, makeCall, addAgent, initialState]
                aesop?
            · cases i using Fin.lastCases
              case last =>
                aesop?
              case cast _ i =>
                simp [initial_call, makeCall, addAgent, initialState]
                aesop?
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
              -- Reusing old have statement that is no longer in scope.
              have know_all_but_last : ∀ (i : Fin (k + 4)), ∀ (j : Fin (k + 4)), makeCalls (addAgent (initialState (k + 4))) (expandCalls seq) i.castSucc j.castSucc := by
                intro i j
                rw [addAgent_replacable]
                simp [addAgent]
                aesop
              have weaker : moreGossip (makeCalls (addAgent (initialState (k + 4))) (expandCalls seq)) (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) (expandCalls seq)) := by
                apply makeCalls_increases_gossip
                apply makeCall_makes_gossip
              apply weaker
              exact know_all_but_last j zero_fin

            have new_agent_learns_a : makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) (expandCalls seq) succ_fin zero_fin := by
              have weaker : moreGossip (makeCall (addAgent (initialState (k + 4))) initial_call) (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) (expandCalls seq)) := by
                apply calls_increase_gossip

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
            case cast foo j =>
              rw [makeCalls_cons] at h''
              exact old_agents_learn_a j
          case fin_succ_knows_own =>
            exact fin_succ_knows_own

        -- Type mismatch, need to fix.
        cases i using Fin.lastCases
        case last => exfalso; tauto
        case cast foo i =>
          exact all_know_new_secret


      -- Putting them together in the right format.
      have final : ∀ (j : Fin (Nat.succ (k + 4))), temp_state i j := by
        intro j
        -- all old agents know the new agent's secret
        have final_secret : temp_state (i.castSucc) succ_fin := by
          aesop

        -- all old agents know all old secrets in the new state
        have other_secrets : ∀ (q : Fin (k + 4)), temp_state i (q.castSucc) := by
          aesop

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
      apply makeCall_makes_gossip

    intro i a j
    simp_all only [ne_eq, new_state]
    apply subgoal_2
    simp_all only [not_false_eq_true]

  -- Using the final call, we can show that the new agent also becomes an expert
  have h_new4 : isExpert new_state succ_fin := by
    have h : isExpert temp_state zero_fin := by
      unfold isExpert
      intro j
      simp_all only [temp_state, calls_without_final_call]
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
