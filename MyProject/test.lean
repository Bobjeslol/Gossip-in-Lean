import Mathlib.Data.List.Basic



/-
Given a call sequence that works for n agents, we only have to add two calls:

(0, n + 1) at the front of the call sequence that worked for n agents, and then (0, n + 1) at the end of the call sequence as well.

This works because we know that the original call sequence makes everyone an expert, when we don't consider n+1's secret. By starting with the call (0, n + 1), agent 0 will know n+1's secret and share it around the group like it was their own. This means that after (0, n + 1) ++ sigma, all agents except agent (n + 1) will be an expert. Agent n + 1 however, only knows their own secret and 0's. So, we have to include one more call at the end so that agent n + 1 becomes an expert as well.


-/


-- Generates an initial state for n agents
def generateState (n : Nat) : (List (List Nat)) :=
  (List.range (n)).map (fun x => [x])

-- Checks if everyone is an expert
def checkIfEE (s : (List (List Nat))) : Bool :=
  let outerLen := s.length
  s.all (fun inner => inner.length = outerLen)

-- Update set index idx of lst to newVal
def updateAtIndex (lst : List (List Nat)) (idx : Nat) (newVal : List Nat) : List (List Nat) :=
  lst.enum.map (λ ix_elem => if ix_elem.fst = idx then newVal else ix_elem.snd)

-- Performs a single call
def performCall (s : List (List Nat)) (caller callee : Nat) : List (List Nat) :=
  match s.get? caller, s.get? callee with
  | some callerList, some calleeList =>
    let mergedList := List.union callerList calleeList
    let sUpdated := updateAtIndex s caller mergedList
    updateAtIndex sUpdated callee mergedList
  | _, _ => s


-- Performs multiple calls
def applyCalls (s : List (List Nat)) (calls : List (Nat × Nat)) : List (List Nat) :=
  calls.foldl (fun acc call => performCall acc call.fst call.snd) s




-- Testing
def initialState := generateState 5
#eval applyCalls initialState [(1, 2), (0, 1), (1,5)]

def seq := [(0, 1), (2, 3), (0, 2), (1, 3)]

-- Proof that is a seq such that checkIfEE returns True
theorem existsStateSatisfiesCheckIfEE : ∃ (state : List (List Nat)), checkIfEE state = True :=
  by exists [[0, 1], [0, 1]]


-- Proof that calls can be made from generatestate 4 that results in a state for which checkifEE state returns true
theorem calls : ∃ (seq : List (Nat × Nat)), checkIfEE (applyCalls (generateState 4) seq) = True :=
  by exists [(0, 1), (2, 3), (0, 2), (1, 3)]


-- Proof that for n = 4 there is a seq with length 4
lemma n_is_four : 4 ≥ 4 → ∃ (seq : List (Nat × Nat)), checkIfEE (applyCalls (generateState 4) seq) = true :=
  by intro _
     exists [(0, 1), (2, 3), (0, 2), (1, 3)]

-- induction for n > 3, base case n = 4
theorem expertSequenceWorks (n : Nat) : (n ≥ 4) → ∃ (seq : List (Nat × Nat)), checkIfEE (applyCalls (generateState n) seq) = true :=
  match n with
  | 0 => fun h => sorry
  | 1 => fun h => sorry
  | 2 => fun h => sorry
  | 3 => fun h => sorry
  | 4 => by exact n_is_four
  | (m + 1) => fun h => sorry
