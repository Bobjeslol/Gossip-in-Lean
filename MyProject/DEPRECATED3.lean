import Mathlib.Data.List.Basic


-- Generates an initial state for n agents
def generateState (n : Nat) : (List (List Nat)) :=
  (List.range (n)).map (fun x => [x])

-- Determines if a knows b's secret
def knowsSecret (a : Nat) (b : Nat) (s : List (List Nat)) : Bool :=
  (s.get! a).contains b

-- Determines if someone is an expert
def isExpert (s : List (List Nat)) (n : Nat) : Bool :=
  (List.range (s.length)).all (fun x => knowsSecret x n s)

-- Checks if everyone is an expert
def checkIfEE (s : (List (List Nat))) : Bool :=
  (List.range (s.length)).all (fun x => isExpert s x)

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
def initialState := generateState 4

#eval applyCalls initialState [(1, 2)]
#eval applyCalls initialState [(1, 2), (0, 1)]
#eval applyCalls initialState [(1, 2), (0, 1), (1,4)]

#eval checkIfEE (applyCalls initialState [(0, 1), (2, 3), (0, 2), (1, 3)])

#eval knowsSecret 3 2 (applyCalls initialState [(1, 2), (0, 1), (1,4)])
#eval knowsSecret 4 2 (applyCalls initialState [(1, 2), (0, 1), (1,4)])

def seq := [(0, 1), (2, 3), (0, 2), (1, 3)]


-- Proof that for n = 4 there is a seq with length 4
lemma n_is_four : 4 ≥ 4 → ∃ (seq : List (Nat × Nat)), checkIfEE (applyCalls (generateState 4) seq) = true := by
     intro _
     exact Exists.intro [(0, 1), (2, 3), (0, 2), (1, 3)] (of_decide_eq_true (Eq.refl true))


-- Extends a sequence of calls to include agent n+1
def extendSequence (seq : List (Nat × Nat)) (n : Nat) : List (Nat × Nat) :=
  [(0, n + 1)] ++ seq ++ [(0, n + 1)]

-- Proof that generateState n + 1 == generatestate n ++ [n+1]
lemma generateStateInductiveStep (n : Nat) : generateState (n + 1) = generateState n ++ [[n]] := by
  induction n
  case zero =>
    simp_all only [Nat.zero_eq, Nat.zero_add]
    rfl
  case succ k IH =>
    simp_all only [Nat.succ_eq_add_one]
    have h : k + 1 + 1 = k + 2 := by rfl
    rw [h]
    rw [← IH]
    sorry

-- -- Lemma that says we can inductively do another step
-- lemma inductiveStep : ∀ (n : Nat), n ≥ 4 →
--     ∃ (seq : List (Nat × Nat)), checkIfEE (applyCalls (generateState n) seq) = true →
--     ∃ (seq' : List (Nat × Nat)), checkIfEE (applyCalls (generateState (n + 1)) (extendSequence seq n)) = true := by
--   intro n
--   intro h
--   use seq
--   intro hseq
--   use extendSequence seq n
--   unfold extendSequence
--   sorry



--Testing
def seqB := [(0, 1)]
#eval (applyCalls (generateState (Nat.succ 0 + 4)) seqB)
#eval isExpert (applyCalls (generateState (Nat.succ 0 + 4)) seqB) 0

lemma inductive_case : ∀ (k : Nat), (Nat.succ k + 4 ≥ 4) → (∃ seq, checkIfEE (applyCalls (generateState (k + 4)) seq) = true) → ∃ seq', checkIfEE (applyCalls (generateState (Nat.succ k + 4)) seq') = true := by
  intro k
  intro h
  intro hseq

  -- There is a sequence such that agent 0 will know all secrets (just add (0, k) at the start)
  have start : ∃ (seqA : List (Nat × Nat)), (List.range k).all (fun x => knowsSecret 0 x (applyCalls (generateState (Nat.succ k + 4)) seqA)) := by
    -- First show that zero knows all secrets from the previous step in hseq
    -- IF EVERYONE IS AN EXPERT, ANY INDIVIDUAL AGENT IS AN EXPERT (HOW TO PROVE??)
    unfold checkIfEE at hseq
    have h_expert_all : ∃ (seq: List (Nat × Nat)), ∀ x, x < k → isExpert (applyCalls (generateState (k + 4)) hseq) x := by
      -- Get a universal quantifier from IH
      rw [List.all_iff_forall_prop] at hseq

    -- then show that we can add (0, k) to the start to make zero a real expert


    sorry


  -- After the final to last call, all agents except k know all secrets
  have h0 : ∃ (seqB : List (Nat × Nat)), (List.range k).all (fun x => isExpert (applyCalls (generateState (Nat.succ k + 4)) seqB) x) := by
    sorry

  -- Final call makes k an expert
  have h1 : ∃ (seqC : List (Nat × Nat)), isExpert (applyCalls (generateState (Nat.succ k + 4)) seqC) k := by
    -- show that from h0 it follows that there is some sequence such that agent 0 knows all secrets
    have h0' : ∃ (seqB : List (Nat × Nat)), isExpert (applyCalls (generateState (Nat.succ k + 4)) seqB) 0 := by
      -- unfold isExpert at h0
      -- Cases where k is 0 or higher
      induction k
      case zero =>
        exists [(0, 1), (2, 3), (0, 2), (1, 3), (0, 4)]
      case succ k IH =>
        -- Have that all agents except k know all but k's secret
        -- REWRITE IH because case 0 does this

        -- Have that we can add call (0, k) at the start to include k's secret so that
        --

        -- have that agent zero knows all but succ k's secret
        have t : ∃ (seqD : List (Nat × Nat)), (List.range k).all (fun x => knowsSecret 0 x (applyCalls (generateState (Nat.succ k + 4)) seqD)) := by
          sorry

        -- There is a call sequence such that agent 0 knows succ k's secret
        have t' : ∃ (seqE : List (Nat × Nat)), knowsSecret 0 (Nat.succ k) (applyCalls (generateState (Nat.succ k + 4)) seqE) := by
          sorry

        -- Combine the two sequences to get a sequence where agent 0 knows all secrets
        have t'' : ∃ (seqF : List (Nat × Nat)),
          (List.range (Nat.succ k)).all (fun x => knowsSecret 0 x (applyCalls (generateState (Nat.succ k + 4)) seqF))
          := by

            sorry -- START HERE

  -- Given sequence that makes all agents except k experts, and a sequence that makes k an expert, we can combine them to make all agents experts
  have h2 : ∃ (seqD : List (Nat × Nat)), checkIfEE (applyCalls (generateState (Nat.succ k + 4)) seqD) = true := by
    sorry

  exact h2

-- induction for n > 3, base case n = 4
theorem expertSequenceWorks (n : Nat) : (n ≥ 4) → ∃ (seq : List (Nat × Nat)), checkIfEE (applyCalls (generateState n) seq) = true :=
  match n with
  | 0 => sorry
  | 1 => sorry
  | 2 => sorry
  | 3 => sorry
  | (m + 4) =>  by
                intro h
                induction m
                case zero =>
                  exists [(0, 1), (2, 3), (0, 2), (1, 3)]
                case succ k IH =>
                  simp at IH
                  -- rcases IH with ⟨ seq, statement ⟩
                  exact inductive_case k h IH
