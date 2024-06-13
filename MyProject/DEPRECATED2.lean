import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic



def GossipState (n : Nat) : Type := Fin n → Fin n → Bool

def Call (n : Nat): Type := (Fin n) × (Fin n) -- probably should remove m

def generateState (n : Nat) : GossipState n :=
  λ i j => i = j

def makeCall (s : GossipState n) (c : Call n) : GossipState n :=
  let (i, j) := c
  λ x y => if x = i then s x y || s j y
           else if x = j then s x y || s i y
           else s x y

def makeCalls (s : GossipState n) (cs : List (Call n)) : GossipState n :=
  cs.foldl makeCall s


def everyoneExpert (s: GossipState n) : Bool :=
  ∀ a b : Fin n, s a b = true

/-- Add an agent to a gossip state, only knowing their own secret. -/
def addAgent (s : GossipState n) : GossipState (n.succ) :=
  λ a b => by
  -- distinguish two cases: (is agent a the new one or an old one)
  cases a using Fin.lastCases
  case last => -- (case 1) if a = n.succ (the new agent)
    exact b == n.succ -- this means a == b and says a only knows their own secret.
  case cast i => -- (case 2) if a = j.castSucc for some j : Fin n (i.e. and old agent)
    -- again distnguish two cases (is agent b the new one or old one)
    cases b using Fin.lastCases
    · exact false -- old agent a should not know secrets of the new agent
    case cast b =>
      exact s i b -- old agent a should know secrets of another old agent b iff that was already the case before.

/-- A shorter way to define (hopefully) the same, as a term instead of a tactic proof. -/
def addAgent' (s : GossipState n) : GossipState (n.succ) :=
  λ a b => Fin.lastCases (b == n.succ)
                         (fun i => Fin.lastCases (false)
                                                 (fun b => s i b) i.castSucc) a


-- TESTING PURPOSES
#eval generateState 5 0 2 -- False
#eval generateState 5 1 1 -- True
#eval makeCall (generateState 5) (1, 2) 2 1-- True
#eval makeCall (makeCall (generateState 5) (1, 2)) (2, 3) 1 3 -- False
#eval makeCall (makeCall (makeCall (generateState 5) (1, 2)) (2, 3)) (3, 5) 5 1 -- True
#eval everyoneExpert (makeCalls (generateState 4) [(1, 2), (3, 4), (1, 3), (2, 4)]) -- True
#eval everyoneExpert (makeCalls (generateState 5) [(1, 5), (1, 2), (3, 4), (1, 3), (2, 4), (1, 5)]) -- True
-- TESTING PURPOSES



-- Shows that after a call ab b also knows all a's secrets.
theorem afterCall_knowsSecret_V (n : Nat) (s : GossipState n) (a b : Fin n) (V : Fin n → Prop) :
  (∀ v : Fin n, V v → s a v) → ∀ v : Fin n, V v → (makeCall s (a, b)) b v :=
  λ h v Vv =>
    if h_eq : b = a then by -- if b = a, then b knows all secrets of a
      rw [h_eq]
      simp [makeCall]
      rw [h v Vv]
    else by
      simp only [makeCall, h_eq]
      rw [h v Vv]
      simp


-- After some arbitrary call, the same information is still available.
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

-- After some arbitrary call sequence, the same information is still available.
lemma knowledge_persists_calls_after (n : ℕ) (σ τ : List (Call n)) (i j k l: Fin n) :
  (makeCall (generateState n) (k, l) i j) →
  (makeCalls (makeCall (generateState n) (k, l)) τ) i j := by
  sorry


-- Before some arbitrary call, the same information is still available.
lemma knowledge_persists_call_before (n : ℕ) (σ : List (Call n)) (i j k l: Fin n) :
  (makeCalls (generateState n) σ i j) →
  (makeCalls (makeCall (generateState n) (k, l)) σ) i j := by
  intro h
  unfold makeCall
  simp
  unfold makeCalls at h
  unfold makeCall at h
  -- unfold generateState at h
  unfold makeCalls
  -- unfold generateState
  unfold makeCall
  unfold List.foldl at h
  unfold List.foldl
  sorry




-- Shows that secrets are not lost if calls are added before or after.
lemma knowledge_persistence {n : ℕ} (σ τ : List (Call n)) (i j : Fin n) :
  (makeCalls (generateState n) σ i j) →
  (makeCalls (generateState n) (τ ++ σ) i j) ∧ (makeCalls (generateState n) (σ ++ τ) i j) := by
  intro h
  induction τ
  case nil =>
    simp
    exact h
  case cons =>
    sorry



-- If after sigma a knows b, then after sigma.(a, i), i knows b.
lemma knowledge_transfer (n : Nat) (σ : List (Call n)) (a i b : Fin n) :
  (makeCalls (generateState n) σ a b) →
  makeCall (makeCalls (generateState n) σ) (a, i) i b := by
  intro h_a_knows_b
  simp [makeCall]
  if h_eq : a = i then
    rw [h_eq]
    simp
    rw [← h_eq]
    exact h_a_knows_b
  else
    -- we know a ! i so just take the else clause
    rw [if_neg]
    induction σ
    case nil =>
      right
      exact h_a_knows_b
    case cons =>
      sorry

def SecretSet (n : Nat) : Type := List (Fin n)
def AgentSet (n : Nat) : Type := List (Fin n)


-- Shows that if an agent a ∈ m knows all secrets in V, and sigma makes all agents in m learn all secrets of m, then after sigma all agents in m know all secrets in V.
theorem effectiveSubsetCommunication (n : Nat) (s : GossipState n) (σ : List (Call n)) (a : Fin n) (m : List (Fin n)) (V : List (Fin n)):
  (a ∈ m) →                     -- a is part of subset m
  (∀ v ∈ V, s a v = true) →     -- a knows all secrets in V
  (∀ a ∈ m, ∀ b ∈ m, makeCalls (generateState n) σ a b = true) → -- then if all agents in m learn all secrets of m
  (∀ b ∈ m, ∀ v ∈ V, makeCalls s σ b v = true) := by
  intro h_a_in_m
  intro h_a_knows_V
  intro h_all_m_learn_all_m
  intro b h_b_in_m
  intro v h_v_in_V
  sorry
