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

-- Prop: are two states identical?
def moreGossip (s1 s2 : GossipState n) : Prop := ∀ a b : Fin n, (s1 a b) → (s2 a b)

-- Adds an agent to a state, that knows only their own secret
def addAgent (s : GossipState n) : GossipState (n.succ) :=
  λ a b => by
  cases a using Fin.lastCases
  case last => -- if a = n.succ (the new agent)
    exact b == n.succ
  case cast i =>
    cases b using Fin.lastCases
    · exact false -- old agent a should not know secrets of the new agent
    case cast b =>
      exact s i b -- old agent a should know secrets of another old agent b iff that was already the case before.

-- Doing a call and some list after is the same as doing a list of calls with that call as its head
lemma makeCalls_cons (s : GossipState n) (c : Call n) (cs : List (Call n)) :
  makeCalls s (c :: cs) = makeCalls (makeCall s c) cs := by
    rfl

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


lemma knowledge_persists_call_after (n : ℕ) (σ : List (Call n)) (i j k l: Fin n) :
  (makeCalls (generateState n) σ i j) → (makeCall (makeCalls (generateState n) σ) (k, l)) i j := by
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

lemma inductive_case : ∀ (k : Nat), (Nat.succ k + 4 ≥ 4) → (∃ seq, checkIfEE (makeCalls (generateState (k + 4)) seq))
  → ∃ seq', checkIfEE (makeCalls (generateState (Nat.succ k + 4)) seq') := by
  intro n h IH
  cases IH
  rename_i k seq IH
  let zero_fin : Fin (k + 5) := Fin.ofNat 0
  let succ_fin : Fin (k + 5) := Fin.ofNat (Nat.succ n)
  let initial_call : List (Call (k + 5))  := [(zero_fin, succ_fin)]
  sorry

  -- We know that there is a sequence of calls that makes everyone an expert
  -- First step is to add a new agent
  -- We know that the new agent knows only their own secret
  -- We know that the old agents know all (old) secrets when call sequence sigma is applied
  -- after adding a new call from agent 0 to the new agent at the start,

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
                  exact inductive_case k h IH
