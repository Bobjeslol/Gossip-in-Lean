import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic


variable {n : ℕ}

def GossipState (n : Nat) : Type := Fin n → Fin n → Prop

def Call (n : Nat): Type := Fin n × Fin n

def generateState (n : Nat) : GossipState n := fun i j => i = j

def makeCall (s : GossipState n) : Call n → GossipState n
| (i, j), x, y =>
    if x = i
      then s x y ∨ s j y
      else
        if x = j
          then s x y ∨ s i y
          else s x y

def makeCalls (s : GossipState n) (cs : List (Call n)) : GossipState n :=
  cs.foldl makeCall s

def everyoneExpert (s : GossipState n) : Prop := ∀ a b : Fin n, s a b

-- Prop: are two states identical?
def moreGossip (s1 s2 : GossipState n) : Prop := ∀ a b : Fin n, s1 a b → s2 a b

-- Doing a call and some list after is the same as doing a list of calls with that call as its head
lemma makeCalls_cons (s : GossipState n) (c : Call n) (cs : List (Call n)) :
    makeCalls s (c :: cs) = makeCalls (makeCall s c) cs := by
    rfl

lemma makeCall_increases_gossip (s1 s2 : GossipState n) (c : Call n) :
    moreGossip s1 s2 → moreGossip (makeCall s1 c) (makeCall s2 c) := by
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
    unhygienic
      aesop_cases
        a_1
    · apply
        Or.inl
      apply
        h
      simp_all only
    · apply
        Or.inr
      apply
        h
      simp_all only
    aesop

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
      have h_call : moreGossip (makeCall s1 head) (makeCall s2 head) := makeCall_increases_gossip s1 s2 head h
      exact ih (makeCall s1 head) (makeCall s2 head) h_call

-- Before some arbitrary call, the same information is still available.
lemma knowledge_persists_call_before (n : ℕ) (σ : List (Call n)) (i j k l: Fin n) :
  (makeCalls (generateState n) σ i j) →
  (makeCalls (makeCall (generateState n) (k, l)) σ) i j := by
  intro h
  apply makeCalls_increases_gossip
  exact makeCall_makes_gossip (generateState n) (k, l)
  exact h


lemma knowledge_persists_call_after (n : ℕ) (σ : List (Call n)) (i j k l: Fin n) :
  (makeCalls (generateState n) σ i j) →
  (makeCall (makeCalls (generateState n) σ) (k, l)) i j := by
  simp [makeCall]
  intro h
  if h_eq : i = k then
    rw [h_eq]
    rw [if_pos]
    left
    rw [← h_eq]
    case h =>
      exact h
    case hc =>
      rfl
  else
    rw [if_neg h_eq]
    if h_eq2 : i = l then
      rw [h_eq2]
      rw [if_pos]
      left
      rw [← h_eq2]
      exact h
      case hc => -- WHY IS THIS NECESSARY????
        rfl
    else
      rw [if_neg h_eq2]
      exact h


-- Next goal, set up the final goal with sorry's and start proving the lemmas.
