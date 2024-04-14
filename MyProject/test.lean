import Mathlib.Data.List.Basic

-- Generates an initial state for n agents
def generateState (n : Nat) : (List (List Nat)) :=
  (List.range (n + 1)).map (fun x => [x])

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


theorem everyone_becomes_expert (n : Nat) (h : n ≥ 4) :
  ∃ calls : List (Nat × Nat), calls.length = 2 * n - 4 ∧ checkIfEE (applyCalls (generateState n) calls) = true :=
by
  induction n with
  | succ n ih =>
    -- Directly address n = 4 (base case) and n > 4 (inductive step) here
    if h1 : n = 3 then
      -- Base case: n = 4
      -- Provide explicit sequence for n = 4 and show it satisfies theorem's conditions
      apply exists.intro seq,
      split,
      { -- Proof for calls.length = 2*4 - 4
        simp,
        exact rfl },
      { -- Proof that checkIfEE returns true for this sequence
        checkIfEE initialState 4 seq
         }
    else
      -- Inductive step: Assume theorem holds for n, prove for n+1
      -- Utilize induction hypothesis (ih) as necessary
      -- Here, handle the construction of calls for n+1 based on n
      -- and prove it satisfies the conditions
      sorry
