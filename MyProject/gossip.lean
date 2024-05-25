import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic

variable {n : ℕ}

def GossipState (n : Nat) : Type := Fin n → Fin n → Prop

def Call (n : Nat): Type := Fin n × Fin n

def generateState (n : Nat) : GossipState n := fun i j => i = j

instance {n : ℕ} : DecidableRel (generateState n) := decEq

-- Determines if someone is an expert
-- a is agent, n is the total number of secrets
def isExpert (s : GossipState n) (i : Fin n): Prop := ∀ j, s i j

instance {s : GossipState n} [DecidableRel s] {i : Fin n} : Decidable (isExpert s i) :=
  Fintype.decidableForallFintype

-- Checks if everyone is an expert
def checkIfEE (s : GossipState n) : Prop := ∀ i, isExpert s i

instance {s : GossipState n} [DecidableRel s] : Decidable (checkIfEE s) :=
  Fintype.decidableForallFintype

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


def makeCalls (s : GossipState n) (cs : List (Call n)) : GossipState n :=
  cs.foldl makeCall s

instance {s : GossipState n} [DecidableRel s] {cs : List (Call n)} :
    DecidableRel (makeCalls s cs) := by
  induction cs generalizing s
  case nil hs => exact hs
  case cons c _ ih hs => exact ih

def everyoneExpert (s : GossipState n) : Prop := ∀ a b : Fin n, s a b

-- Prop: s2 contains equal or more gossip to s1
def moreGossip (s1 s2 : GossipState n) : Prop := ∀ a b : Fin n, (s1 a b) → (s2 a b)

-- Adds an agent to a state, that knows only their own secret
def addAgent (s : GossipState n) : GossipState (n.succ) :=
  λ a b => Fin.lastCases (b == Fin.last n)
                         (fun i => Fin.lastCases (false)
                                                 (fun b => s i b)
                                                b) a

-- Given a call fin n, return the same call fin (n + 1)
def expandCall {n : ℕ} (c : Call n) : Call (Nat.succ n) := match c with
  | (i, j) => (i, j)

-- Given a sequence of calls, return the same sequence of calls in fin (n + 1)
def expandCalls {n : ℕ} (cs : List (Call n)) : List (Call (Nat.succ n)) :=
  cs.map expandCall

def stateEquivalence : GossipState n → GossipState n → Prop :=
  λ s1 s2 => ∀ a b, s1 a b ↔ s2 a b

lemma addAgent_old_old {s : GossipState n} {i j : Fin n} :
    addAgent s i.castSucc j.castSucc ↔ s i j := by
    simp [addAgent]

lemma addAgent_old_new {s : GossipState n} {i : Fin n} :
    ¬ addAgent s i.castSucc (Fin.last n) := by
    simp only [addAgent, beq_self_eq_true, Fin.lastCases_last, Fin.lastCases_castSucc,
      not_false_eq_true]

lemma addAgent_new_old {s : GossipState n} {i : Fin n} :
    ¬ addAgent s (Fin.last n) i.castSucc := by
    simp [addAgent]
    cases i
    simp [Fin.castSucc, Fin.last]
    intro a
    subst a
    simp_all only [lt_self_iff_false]

lemma addAgent_new_new {s : GossipState n} {i : Fin n} :
    addAgent s (Fin.last n) (Fin.last n) := by
    simp [addAgent]

-- Doing a call and some list after is the same as doing a list of calls with that call as its head
lemma makeCalls_cons (s : GossipState n) (c : Call n) (cs : List (Call n)) :
  makeCalls s (c :: cs) = makeCalls (makeCall s c) cs := by
    rfl

-- Doing a list of calls and then a call is the same as doing the list of calls with the call as its tail
lemma makeCalls_snoc (s : GossipState n) (cs : List (Call n)) (c : Call n) :
  makeCalls s (cs ++ [c]) = makeCall (makeCalls s cs) c := by
    induction cs generalizing s
    case nil => rfl
    case cons c' cs ih => simp [makeCalls, ih]


lemma makeCall_increases_gossip (s1 s2 : GossipState n) (c : Call
n) : moreGossip s1 s2 → moreGossip (makeCall s1 c) (makeCall s2 c) := by
    intro h
    intro a b
    simp [makeCall]
    intro a_1
    simp_all only
    split
    simp_all only
    split
    rename_i
      x
      x_1
      x_2
      i
      j
      h_1
    aesop_subst
      h_1
    simp_all only [↓reduceIte]
    aesop?
    aesop?


-- doing a call doesnt decrease the amount of gossip
lemma makeCall_makes_gossip (s : GossipState n) (c : Call n) :
    moreGossip s (makeCall s c) := by
  unfold moreGossip
  intro a b
  intro h
  simp [makeCall]
  simp_all only
  split
  simp_all only
  split
  rename_i x x_1 x_2 i j h_1
  aesop_subst
    h_1
  simp_all only [true_or]
  rename_i c f g i j k
  if hyp: a = j then
    rw [hyp]
    rw [if_pos]
    aesop_subst
      hyp
    simp_all only [true_or]
    case hc =>
      rfl
  else
    rw [if_neg]
    simp_all only
    exact hyp

lemma makeCalls_increases_gossip (s1 s2 : GossipState n) (cs : List (Call n)) :
    moreGossip s1 s2 → moreGossip (makeCalls s1 cs) (makeCalls s2 cs) := by
    intro h
    induction cs generalizing s1 s2
    case nil =>
      simp [makeCalls]
      exact h
    case cons head tail ih =>
      rw [makeCalls_cons, makeCalls_cons]
      have h_call : moreGossip (makeCall s1 head) (makeCall s2
      head) := makeCall_increases_gossip s1 s2 head h
      exact ih (makeCall s1 head) (makeCall s2 head) h_call

-- Before some arbitrary call, the same information is still available.
lemma knowledge_persists_call_before (n : ℕ) (σ : List (Call n))
(i j k l: Fin n) :
  (makeCalls (generateState n) σ i j) →
  (makeCalls (makeCall (generateState n) (k, l)) σ) i j := by
  intro h
  apply makeCalls_increases_gossip
  exact makeCall_makes_gossip (generateState n) (k, l)
  exact h

-- After some arbitrary call, the same information is still available.
lemma knowledge_persists_call_after (n : ℕ) (i j k l: Fin n)
    (s : GossipState n) : s i j → (makeCall s (k, l)) i j := by
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

-- States that adding an agent to a state doesn't decrease the amount of gossip
-- UNUSED
lemma addAgent_doesnt_decrease_gossip (s1 s2 : GossipState n) :
  moreGossip s1 s2 → moreGossip (addAgent s1) (addAgent s2) := by
  intro h
  intro a b
  simp [addAgent]
  intro h1
  sorry

-- Any experts in the old state know all secrets in the new state
lemma addAgent_expert_old {s : GossipState n} {i : Fin n} :
  isExpert s i → ∀ j : Fin n, addAgent s i j := by
  intro h
  intro j
  simp [isExpert] at h
  simp [addAgent]
  simp_all only

-- IS THIS EVEN DOABLE?
-- We can replace addAgent with generateState (n + 1) in the following lemma n ≥ 4
lemma addAgent_equals_succ {n : ℕ} :
  addAgent (generateState n) = (generateState (Nat.succ n)) := by
  induction n
  case zero =>
    simp [addAgent, generateState]
    unfold generateState
    unfold addAgent
    simp
    unfold Fin.last
    simp_all
    funext
    funext
    aesop?
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
    unfold generateState
    funext i
    cases i
    simp_all only [Fin.castSucc, Fin.last]
    case h.mk =>
      simp [Fin.lastCases]
      simp [Fin.reverseInduction]
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

-- Need this one done..
lemma makeCalls_addAgent_generateState_equiv {n : Nat} (initial_call : Call (n + 1)) (expandedSeq : List (Call (n + 1))) :
  makeCall (makeCalls (makeCall (addAgent (generateState n)) initial_call) expandedSeq) initial_call =
  makeCalls (generateState (n + 1)) ([initial_call] ++ expandedSeq ++ [initial_call]) := by
  rw [← makeCalls_cons]
  rw [addAgent_equals_succ] -- for this n has to be at least 4...
  rw [makeCalls_snoc]
  simp_all only [List.singleton_append]


--Unused, kept for reference
lemma inductive_case : ∀ (k : Nat), (Nat.succ k + 4 ≥ 4) → (∃ seq, checkIfEE (makeCalls (generateState (k + 4)) seq))
  → ∃ seq', checkIfEE (makeCalls (generateState (Nat.succ k + 4)) seq') := by
  intro n h IH
  cases IH
  rename_i seq IH
  let expandedSeq := expandCalls seq
  let zero_fin : Fin (Nat.succ n + 4) := Fin.ofNat 0
  let succ_fin : Fin (Nat.succ n + 4) := Fin.last (n + 4) -- Maybe nat.succ on n? i think this works though
  let initial_call : Call (Nat.succ n + 4)  := (zero_fin, succ_fin)
  let new_state := makeCall (makeCalls (makeCall (addAgent (generateState (n + 4))) initial_call) expandedSeq) initial_call


  -- Need lemma to show addAgent (generateState (n + 4)) is equal to generateState (n + 4 + 1)
  -- First new_state into a single sequence of calls that only needs one makeCalls application
  have single_calls : new_state = makeCalls (generateState (Nat.succ n + 4)) ([initial_call] ++ expandedSeq ++ [initial_call]) := by
    sorry

  -- in new_state, the first agent knows the secret of the new agent due to the initial call
  have h_new : new_state zero_fin succ_fin := by
    simp [new_state]
    left
    apply makeCalls_increases_gossip (addAgent (generateState (n + 4))) (makeCall (addAgent (generateState (n + 4))) initial_call)
    sorry

  -- in new_state, the first n agents know all secrets of the first n agents using the original seq
  have h_new1 : ∀ i, new_state zero_fin i := by
    sorry

  -- thus, the first n agents all learn the secret of the new agent as well due to the initial call followed by seq
  have h_new2 : ∀ i, new_state i succ_fin := by
    sorry

  -- Putting h_new1 and h_new2 together, we get that all but the last agents are experts
  have h_new3 : ∀ i, i ≠ succ_fin → isExpert new_state i := by
    sorry

  -- using the final call, we can show that the new agent also becomes an expert
  have h_new4 : isExpert new_state succ_fin := by
    sorry

  -- putting h_new3 and h_new4 together, we get that everyone is an expert
  have h_new5 : checkIfEE new_state := by
    unfold checkIfEE
    intro i
    cases i
    rename_i val isLt
    let i_rebuilt : Fin (Nat.succ (n + 4)) := ⟨val, isLt⟩
    by_cases (i_rebuilt = succ_fin);
    rename_i
      n_1
      h_1
    simp_all only [ge_iff_le,
      le_add_iff_nonneg_left,
      zero_le,
      List.singleton_append,
      List.cons_append,
      ne_eq,
      new_state,
      initial_call,
      zero_fin,
      succ_fin,
      expandedSeq,
      i_rebuilt]
    rename_i
      n_1
      h_1
    simp_all only [ge_iff_le,
      le_add_iff_nonneg_left,
      zero_le,
      List.singleton_append,
      List.cons_append,
      ne_eq,
      not_false_eq_true,
      new_state,
      initial_call,
      zero_fin,
      succ_fin,
      expandedSeq,
      i_rebuilt]

  -- thus in new_state everyone is an expert, and since new_state is equal to single_calls which is
  -- the result of a single makeCalls application we have found a sequence that works
  exists [initial_call] ++ expandedSeq ++ [initial_call]
  rw [single_calls] at h_new5
  exact h_new5

lemma inductive_case' : ∀ (k : Nat),
    (∃ seq, checkIfEE (makeCalls (generateState k) seq))
  → ∃ seq', checkIfEE (makeCalls (generateState (k + 1)) seq') := by
  intro n IH
  cases IH
  rename_i seq IH
  let expandedSeq := expandCalls seq
  let zero_fin : Fin (Nat.succ n) := Fin.ofNat 0
  let succ_fin : Fin (Nat.succ n) := Fin.last (n)
  let initial_call : Call (Nat.succ n)  := (zero_fin, succ_fin)
  let attempt := makeCall (addAgent (generateState (n))) initial_call
  let new_state := makeCall (makeCalls (makeCall (addAgent (generateState (n))) initial_call) expandedSeq) initial_call

  have single_calls : new_state = makeCalls (generateState (Nat.succ n)) ([initial_call] ++ expandedSeq ++ [initial_call]) := by
    simp [new_state]
    apply makeCalls_addAgent_generateState_equiv

    -- in new_state, the first n agent knows all secrets of the first n agents using the original seq
  have h_new1 : ∀ i, new_state zero_fin i := by
    -- use addAgent_expert_old
    unfold checkIfEE at IH
    sorry



  -- the first n agent learns the secret of the new agent as well due to the initial call followed by seq
  have h_new2 : ∀ i, new_state i succ_fin := by
    sorry

  -- Thus the first agent is an expert

  -- Putting h_new1 and h_new2 together, we get that all but the last agents are experts
  have h_new3 : ∀ i, i ≠ succ_fin → isExpert new_state i := by
    sorry

  -- using the final call, we can show that the new agent also becomes an expert
  have h_new4 : isExpert new_state succ_fin := by
    simp [new_state]
    sorry

  -- putting h_new3 and h_new4 together, we get that everyone is an expert
  have h_new5 : checkIfEE new_state := by
    unfold checkIfEE
    intro i
    cases i
    rename_i val isLt
    let i_rebuilt : Fin (Nat.succ n) := ⟨val, isLt⟩
    by_cases (i_rebuilt = succ_fin);
    aesop?
    aesop?

  exists [initial_call] ++ expandedSeq ++ [initial_call]
  rw [single_calls] at h_new5
  exact h_new5

-- induction for n > 3, base case n = 4
theorem expertSequenceWorks (n : Nat) : (n ≥ 4) → ∃ (seq : List (Call n)), checkIfEE (makeCalls (generateState n) seq) :=
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
                  exact inductive_case' (k + 4) IH
