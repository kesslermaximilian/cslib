module

public import Cslib.Computability.Machines.SingleTapeTuring.Basic
public import Cslib.Computability.Machines.SingleTapeTuring.TMCook
public import Mathlib.Data.Int.Range
public import Mathlib.Tactic.Linarith
public import Std.Sat.CNF



namespace Std.Sat

-- TODO: These tags are very useful for this file, is this semantic?
attribute [local simp] CNF.not_VarMem_empty
attribute [local simp] CNF.VarMem_append

def CNF.flatten {α : Type*} : List (CNF α) →  CNF α
  | .nil => CNF.empty
  | .cons f fs => f ++ (flatten fs)

@[simp]
lemma CNF.VarMem_flatten {α : Type*} (fs : List (CNF α)) (v : α) :
    CNF.VarMem v (CNF.flatten fs) ↔ ∃ f ∈ fs, CNF.VarMem v f := by
  induction fs with
  | nil => simp [CNF.flatten]
  | cons f fs ih => simp [flatten, ih]

@[simp]
lemma CNF.eval_flatten {α : Type*} (fs : List (CNF α)) (a : α → Bool) :
    CNF.eval a (CNF.flatten fs) = fs.all (fun f => CNF.eval a f) := by
  induction fs with
  | nil => simp [CNF.flatten]
  | cons f fs ih => simp [CNF.flatten, ih]

end Std.Sat



namespace Turing

namespace Cook
open Std.Sat
open BiTape
-- Let us "fix" a finite alphabet `Symbol`
variable {Symbol : Type} [Fintype Symbol]


-- We make arbitrary choices here to order the elements of the alphabet of Symbol
noncomputable section

/- The tape alphabet of the verifier for a language on `Symbol`:
- Contains a blank symbol (represented as `none`) for the tape
- Contains a separator symbol (represented as `some none`) to separate instance and certificate in
  the input
- Contains `Symbol` (repsented as `some (some a))`) to encode the instance -/

-- TODO: Okay to disable this locally?
set_option quotPrecheck false in
/-- Notation for the separator symbol of the tape alphabet -/
notation "#₀" => (some none : (Option (Option Symbol)))

set_option quotPrecheck false in
/-- Notation for the blank symbol of the tape alphabet -/
notation "␣" => (none : Option (Option Symbol))

/-- List of all symbols of `Symbol`, embedded into alphabet `Symbol'` -/
@[grind]
def instanceSymbols : List (Option (Option Symbol)) := Fintype.elems.toList.map (some ∘ some)
/-- List of all input symbols, i.e. `Symbol` and `#₀`, embedded into alphabet `Symbol'` -/
def inputSymbols : List (Option (Option Symbol)):= #₀ :: instanceSymbols
/-- List of all symbols of the tape alphabet `Symbol' = Option (Option Symbol)` -/
def symbols : List (Option (Option Symbol)) := ␣ :: inputSymbols

@[simp]
lemma symbols.complete (a : (Option (Option Symbol))) : a ∈ symbols := by
  match a with
  | none => simp [symbols]
  | some none => simp [symbols, inputSymbols]
  | some (some s) => simp [symbols, inputSymbols, instanceSymbols, Fintype.complete]

-- In addition, let us fix a turing machine `Symbol ∪ {#₀}`
variable (tm : SingleTapeTM (Option Symbol))

/-- List of all states of the turing machine. -/
def states : List (Option tm.State) := none :: tm.stateFintype.elems.toList.map Option.some

@[simp]
lemma states.complete (s : Option tm.State) : s ∈ states tm := by
  cases s <;>
    simp [states, Fintype.complete]

/-- Returns the list of all pairs `(a, b)`, where `a, b ∈ l` and `a ≠ b` -/
def NoneqPairs {α : Type*} [DecidableEq α] (l : List α) : List (α × α) :=
  List.product l l |> List.filter fun (a, b) => decide (a ≠ b)

@[simp]
lemma NoneqPairs.mem_iff {α : Type*} [DecidableEq α] (l : List α) (a b : α) :
    (a, b) ∈ NoneqPairs l ↔ a ∈ l ∧ b ∈ l ∧ a ≠ b := by
  simp [NoneqPairs, and_assoc]

/-- Index used for the variables present in the SAT encoding of a TM0 -/
inductive VarIndex where
  /-- Encodes that at time `t`, at index `n`, the tape contains symbol `a` -/
  | tape  (t : ℕ) (n : ℤ) (a : Option (Option Symbol))
  /-- Encodes that at time `t`, the machine is in state `s` and reading index `n`
    As usual, `none` represents the halting state.
   -/
  | state (t : ℕ) (n : ℤ) (s : Option tm.State)


namespace Encoding
open SingleTapeTM
variable [DecidableEq Symbol] [DecidableEq tm.State]

-- Q is meant to be an upper bound for the tape indices used.
variable (Q : ℕ)
-- C is the length of input certificate.
variable (C : ℕ)
-- accept is the special symbol signaling that the TM accepts, i.e. the single
-- non-blank symbol at the time of termination of the TM.
variable (accept : Symbol)
-- The input instance of the initial language we are verifying
variable (inst : List Symbol)
-- In total, we assume that
-- `inst.length + C ≤ Q`
-- is satisfied, so that the whole input state is captured by our SAT
-- (note that we view the tape indices as the closed interval `[-Q, Q]`, so we can write
-- the input of length `inst.length + 1 + C ≤ Q + 1` on the tape indices `[0, Q]`)

/-- The possible indices for the tape, indexed `-Q,..., Q` -/
@[grind]
def tapeIndices : List ℤ := Int.range (- Q) (Q + 1)

/-- The possible indices for the tape, except `-Q` and `Q`.
Only for these we need to update states. -/
@[grind]
def innerTapeIndices : List ℤ := Int.range (- Q + 1) Q

/-- List of indices where the instance will be written -/
@[grind]
def instanceIndices : List ℤ := Int.range 0 inst.length

/-- Index of the separator symbol on the inital tape -/
@[grind]
def separatorIndex : ℤ := inst.length

/-- List of indices where the certificate will be written -/
@[grind]
def certificateIndices : List ℤ := Int.range (inst.length + 1) (inst.length + C + 1)

/-- List of indices that are initially blank -/
@[grind]
def blankIndices : List ℤ := Int.range (-Q) 0 ++ Int.range (inst.length + C + 1) (Q + 1)


/-- At time `t`, there is a symbol on tape position `n` -/
def SymbolExists (t : ℕ) (n : ℤ) : CNF (VarIndex tm) :=
  ⟨⟨[
    symbols
    |> List.map fun a => (VarIndex.tape t n a, true)
  ]⟩⟩

/-- At time `t`, the symbol on tape position `n` is unique -/
def SymbolUnique (t : ℕ) (n : ℤ) : CNF (VarIndex tm) :=
  ⟨⟨symbols
      |> NoneqPairs
      |> List.map fun (a, b) => [(VarIndex.tape t n a, false), (VarIndex.tape t n b, false)]
  ⟩⟩

/-- At time `t`, there is a state `s` and tape position `n` for the head -/
def StateExists (t : ℕ) : CNF (VarIndex tm) :=
  ⟨⟨[
    List.product (states tm) (tapeIndices Q)
      |> List.map fun (s, n) => (VarIndex.state t n s, true)
  ]⟩⟩

/-- At time `t`, the pair `(s, n)` of state and tape position is unique -/
def StateUnique (t : ℕ) : CNF (VarIndex tm) where
  clauses := { toList :=
    List.product (states tm) (tapeIndices Q)
      |> NoneqPairs
      |> List.map fun ⟨(s, n), (s', n')⟩ =>
        [(VarIndex.state t n s, false), (VarIndex.state t n' s', false)]
  }

/-- When transitioning `t ↦ t + 1` and the machine is in state `s`,
  the state and r/w position is correctly updated (depending on the tape symbol) -/
def UpdateState (t : ℕ) (n : ℤ) (a : (Option (Option Symbol))) (s : Option tm.State) :
    CNF (VarIndex tm) :=
  ⟨⟨[[
    (VarIndex.tape t n a, false),
    (VarIndex.state t n s, false),
    (VarIndex.state (t + 1) (n + posChange (tm.tr' s a).fst.movement) (tm.tr' s a).snd, true)
  ]]⟩⟩

/-- When transitioning `t ↦ t + 1`, the tape at the r/w head is correctly updated -/
def UpdateTape (t : ℕ) (n : ℤ) (a : (Option (Option Symbol))) (s : Option tm.State) :
    CNF (VarIndex tm) :=
  ⟨⟨[[
    (VarIndex.tape t n a, false),
    (VarIndex.state t n s, false),
    (VarIndex.tape (t + 1) n (tm.tr' s a).fst.symbol, true)
  ]]⟩⟩

/-- When transitioning `t ↦ t + 1`, the tape *not* at the r/w head is left unchanged -/
def KeepTape (t : ℕ) (n : ℤ) (a : (Option (Option (Symbol)))) (s : Option tm.State) :
    CNF (VarIndex tm) :=
  ⟨⟨
  tapeIndices Q
    |> List.filter (fun n' => decide (n' ≠ n))
    |> List.map fun n' => [(VarIndex.tape t n a, false), (VarIndex.state t n' s, false),
      (VarIndex.tape (t + 1) n a, true)]
  ⟩⟩

/-- At time `0`, the instance is written on the tape -/
def InitInstance : CNF (VarIndex tm) :=
  ⟨⟨
  inst.zipIdx.map fun (a, n) => [(VarIndex.tape 0 n (some (some a)), true)]
  ⟩⟩

/-- At time `0`, the separator is written behind the instance -/
def InitSeparator : CNF (VarIndex tm) :=
  ⟨⟨[[(VarIndex.tape 0 (inst.length) #₀, true)]]⟩⟩

/-- At time `0`, *any* certificate consisting only of symbols of `Γ` is written behind
 the separator symbol -/
def InitCertificate : CNF (VarIndex tm) :=
  ⟨⟨
    certificateIndices C inst
    |> List.map fun n => instanceSymbols.map fun a => (VarIndex.tape 0 n a, true)
  ⟩⟩

/-- At time `0`, the rest of the tape contains only blank symbols -/
def InitBlank : CNF (VarIndex tm) :=
  ⟨⟨blankIndices Q C inst
    |> List.map fun n => [(VarIndex.tape 0 n ␣, true)]
  ⟩⟩

/-- At time `0`, the state is correctly initialized -/
def InitState : CNF (VarIndex tm) :=
  ⟨⟨[[(VarIndex.state 0 0 (some default), true)]]⟩⟩

/-- At time `0`, the tape and state are correctly initialized -/
def Init : CNF (VarIndex tm) :=
  InitState tm ++ InitInstance tm inst ++ InitSeparator tm inst ++ InitCertificate tm C inst
   ++ InitBlank tm Q C inst

/-- At time `Q`, the r/w head reads `(accept : Symbol)` -/
def Output₀ : CNF (VarIndex tm) :=
  ⟨⟨
  tapeIndices Q
    |> List.map fun n =>
      [(VarIndex.state Q n none, false), (VarIndex.tape Q n (some (some accept)), true)]
  ⟩⟩

/-- At time `Q`, the rest of the tape is filled with blanks. -/
def Output₁ : CNF (VarIndex tm) :=
  ⟨⟨NoneqPairs (tapeIndices Q)
    |> List.map fun (n, m) =>
      [(VarIndex.state Q n none, false), (VarIndex.tape Q m ␣, true)]
  ⟩⟩

def Output : CNF (VarIndex tm) :=
  Output₀ tm Q accept ++ Output₁ tm Q

/-- At time `t`, assignment of symbols, state and r/w position is well-defined -/
def WellDefined₀ (t : ℕ) : CNF (VarIndex tm) :=
  (tapeIndices Q).map (fun n => SymbolExists tm t n)
  ++
  ((tapeIndices Q).map (fun n => SymbolUnique tm t n))
  ++
  [StateExists tm Q t]
  ++
  [StateUnique tm Q t]
    |> CNF.flatten

/-- Assignment of symbols, state and r/w position is well-defined -/
def WellDefined : CNF (VarIndex tm) :=
  List.range (Q + 1)
    |> List.map (fun t => WellDefined₀ tm Q t)
    |> CNF.flatten

/-- When transitioning `t ↦ t + 1`, tape is correctly updated -/
def Propagate₀ (t : ℕ) : CNF (VarIndex tm) :=
  List.product (List.product (tapeIndices Q) symbols) (states tm)
    |> List.map (fun ((n, a), s) => UpdateTape tm t n a s ++ KeepTape tm Q t n a s)
    |> CNF.flatten

/-- When transitioning `t ↦ t + 1`, state is correctly updated -/
def Propagate₁ (t : ℕ) : CNF (VarIndex tm) :=
  List.product (List.product (innerTapeIndices Q) symbols) (states tm)
    |> List.map (fun ((n, a), s) => UpdateState tm t n a s)
    |> CNF.flatten

/-- Propagation of state and tape `0 ↦ 1 ↦ ... ↦ Q` -/
def Propagate : CNF (VarIndex tm) :=
  -- Note that this is range [0, Q), since there is no propagation *step* `Q ↦ Q + 1`
  List.range Q
    |> List.map (fun t => Propagate₀ tm Q t ++ Propagate₁ tm Q t)
    |> CNF.flatten


/-- The total SAT formulation of the execution of the verifier turing machine,
  assuming that
  - Instance `inst` was input
  - Any certificate of length `C` is input
  - Total input length `inst.length + 1 + C` is strictly less than `Q`
  - Execution of the TM takes at most `Q` steps to terminate
  - The r/w head is always in the range `[-Q, Q]`
  - The machine is expected to output `1`, i.e. there exists a certificate for `inst`
-/
def TMSAT (Q C : ℕ) (inst : List Symbol) (accept : Symbol) : CNF (VarIndex tm) :=
  Encoding.WellDefined tm Q ++ Encoding.Propagate tm Q ++ Encoding.Init tm Q C inst
  ++ Encoding.Output tm Q accept

lemma tapeIndices.mem_iff (n : ℤ) :
    n ∈ tapeIndices Q ↔ n ∈ Set.Icc (- (Q : ℤ)) Q := by
  simp only [tapeIndices, Int.mem_range_iff, Int.lt_add_one_iff, Set.mem_Icc]

/-- Characterization whether a variable appears in the SAT formulation:
A variable occurs if and only if it talks about a time `≤ Q` and a tape position
of `tapeIndices Q` -/
def TMSAT.mem (Q : ℕ) (v : VarIndex tm) : Prop :=
  match v with
  | VarIndex.state t n _ => t ≤ Q ∧ n ∈ tapeIndices Q
  | VarIndex.tape t n _ => t ≤ Q ∧ n ∈ tapeIndices Q

@[simp]
lemma CNF.Clause.mem_map {α β : Type*} (v : α) (l : List β) (f : β → Literal α) :
    CNF.Clause.Mem v (l.map f) ↔ ∃ x ∈ l, f x = (v, true) ∨ f x = (v, false) := by
  simp [CNF.Clause.Mem]
  grind

section TMSAT_VarMem
attribute [local grind =] Int.mem_range_iff

lemma innerTapeIndices_posChange (Q : ℕ) (n : ℤ) (h : n ∈ innerTapeIndices Q) (dir : Option Dir) :
    n + posChange dir ∈ tapeIndices Q := by
  grind [SingleTapeTM.posChange_abs_bound dir]

lemma Mem_WellDefined_aux₀ (Q : ℕ) (v : VarIndex tm) :
    CNF.VarMem v (WellDefined tm Q) → TMSAT.mem tm Q v := by
  cases v
  all_goals
    simp only [WellDefined, WellDefined₀, List.append_assoc, List.cons_append, List.nil_append,
      CNF.VarMem_flatten, List.mem_map, List.mem_range, Order.lt_add_one_iff,
      exists_exists_and_eq_and, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      TMSAT.mem, forall_exists_index, and_imp]
    rintro _ _ _ (⟨_, _, heq⟩ | ⟨_, _, heq⟩ | heq | heq) hmem
    all_goals
      simp [heq, ← heq, CNF.VarMem, StateExists, StateUnique, SymbolUnique, SymbolExists] at hmem
      try grind

lemma Mem_WellDefined_aux₁ (Q : ℕ) (v : VarIndex tm) :
    TMSAT.mem tm Q v → CNF.VarMem v (WellDefined tm Q) := by
  unfold TMSAT.mem
  cases v
  all_goals
    intro ⟨ht, hn⟩
    simp only [WellDefined, WellDefined₀, List.append_assoc, List.cons_append, List.nil_append,
      CNF.VarMem_flatten, List.mem_map, List.mem_range, Order.lt_add_one_iff,
      exists_exists_and_eq_and, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  case state t _ _ =>
    refine ⟨t, by linarith, StateExists tm Q t, ?_⟩
    simp [StateExists, CNF.VarMem, states.complete, hn]
  case tape t n _ =>
    refine ⟨t, by linarith, SymbolExists tm t n, ?_⟩
    simp [SymbolExists, CNF.VarMem, symbols.complete, hn]

lemma Mem_TMSAT_aux₀ (Q C : ℕ) (inst : List Symbol) (accept : Symbol) (v : VarIndex tm)
    (h : inst.length + 1 + C ≤ Q) :
    CNF.VarMem v (TMSAT tm Q C inst accept) → TMSAT.mem tm Q v := by
  cases v
  all_goals
    simp only [TMSAT.mem, TMSAT, Init, CNF.VarMem_append, or_assoc]
    rintro (h | h | h | h | h | h | h | h)
    · exact Mem_WellDefined_aux₀ tm Q _ h
    · simp only [Propagate, Propagate₀, Propagate₁, CNF.VarMem_flatten, List.mem_map,
        List.mem_range, exists_exists_and_eq_and, CNF.VarMem_append, Prod.exists,
        List.pair_mem_product, ↓existsAndEq, and_true] at h
      obtain ⟨_, _, ⟨_, _, ⟨_, ⟨_, hmem | hmem⟩⟩⟩ | ⟨n, a, ⟨s, hnas, hmem⟩⟩⟩ := h
      <;> simp [UpdateTape, KeepTape, UpdateState, CNF.VarMem] at hmem
      · grind
      · grind
      · grind [innerTapeIndices_posChange Q _ hnas.left.left (tm.tr' s a).1.movement]
    all_goals
      simp [InitState, InitInstance, InitSeparator, InitCertificate, InitBlank, Output,
        Output₀, Output₁] at h
      simp [CNF.VarMem] at h
      try grind

lemma Mem_TMSAT_aux₁ (Q C : ℕ) (inst : List Symbol) (accept : Symbol) (v : VarIndex tm) :
    TMSAT.mem tm Q v → CNF.VarMem v (TMSAT tm Q C inst accept) := by
  simp only [TMSAT, CNF.VarMem_append]
  have := Mem_WellDefined_aux₁ tm Q v
  grind

theorem Mem_TMSAT (Q C : ℕ) (inst : List Symbol) (accept : Symbol)
    (h : inst.length + 1 + C ≤ Q) (v : VarIndex tm) :
    CNF.VarMem v (TMSAT tm Q C inst accept) ↔ TMSAT.mem tm Q v :=
  ⟨Mem_TMSAT_aux₀ tm Q C inst accept v h, Mem_TMSAT_aux₁ tm Q C inst accept v⟩

end TMSAT_VarMem
end Encoding

open Encoding
variable {tm : SingleTapeTM (Option Symbol)}
variable [DecidableEq Symbol] [DecidableEq tm.State]

/-- An assignment `a` is *normalized* if
- The r/w is always within [-Q, Q]
- The tape is always supported by [-Q, Q]
- The assignment of tape / state is constant after time Q
-/
structure IsNormalized (a : VarIndex tm → Bool) (Q : ℕ) where
  state_normalized : ∀ n ∉ tapeIndices Q, ∀ t q, a (VarIndex.state t n q) = false
  tape_normalized : ∀ n ∉ tapeIndices Q, ∀ t s, a (VarIndex.tape t n s) = true ↔ s = ␣
  state_eventually_const : ∀ t > Q, ∀ n q, a (VarIndex.state t n q) = a (VarIndex.state Q n q)
  tape_eventually_const : ∀ t > Q, ∀ n s, a (VarIndex.tape t n s) = a (VarIndex.tape Q n s)

/-- A normalized assignment `a` is *suitable*, if it satisfies the `WellDefined tm Q` portion of
`TMSAT`. This allows to (uniquely) reconstruct configurations from the assignment.
-/
structure IsSuitable (a : VarIndex tm → Bool) (Q : ℕ) extends IsNormalized a Q where
  well_defined : CNF.Sat a (WellDefined tm Q)

lemma assignment_tape_exists_aux (a : VarIndex tm → Bool) (Q : ℕ)
    (hs : CNF.Sat a (WellDefined tm Q)) :
    ∀ t ≤ Q, ∀ n ∈ tapeIndices Q, ∃! s, a (VarIndex.tape t n s) = true := by
  intro t ht n hn
  simp only [CNF.Sat, WellDefined, WellDefined₀, List.append_assoc, List.cons_append,
    List.nil_append, CNF.eval_flatten, List.all_map, List.all_eq_true, List.mem_range,
    Order.lt_add_one_iff, Function.comp_apply, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true] at hs
  obtain ⟨he, hu, _, _⟩ := hs t ht
  apply existsUnique_of_exists_of_unique
  · simpa [SymbolExists, CNF.eval, CNF.Clause.eval] using he n hn
  · specialize hu n hn
    simp [SymbolUnique, CNF.eval, CNF.Clause.eval] at hu
    grind

lemma assignment_tape_exists (a : VarIndex tm → Bool) {Q : ℕ} (hs : IsSuitable a Q) :
    ∀ t n,  ∃! s, a (VarIndex.tape t n s) = true := by
  intro t n
  wlog ht : t ≤ Q
  · simp [hs.tape_eventually_const t (by linarith) n, this _ hs]
  · by_cases hn : n ∈ tapeIndices Q
    · exact assignment_tape_exists_aux a Q hs.well_defined t ht n hn
    · simp [hs.tape_normalized n hn]

lemma assignment_state_exists' (a : VarIndex tm → Bool) {Q : ℕ} (hs : IsSuitable a Q) :
    ∀ t, ∃! (pos_state : (Set.Icc (α := ℤ) (-Q) Q) × Option tm.State),
      a (VarIndex.state t pos_state.1 pos_state.2) = true := by
  intro t
  wlog ht : t ≤ Q
  · simp [hs.state_eventually_const t (by linarith), this _ hs]
  · have hw := hs.well_defined
    simp only [CNF.Sat, WellDefined, WellDefined₀, List.append_assoc, List.cons_append,
      List.nil_append, CNF.eval_flatten, List.all_map, List.all_eq_true, List.mem_range,
      Order.lt_add_one_iff, Function.comp_apply, List.all_append, List.all_cons, List.all_nil,
      Bool.and_true, Bool.and_eq_true] at hw
    obtain ⟨_, _, he, hu⟩ := hw t ht
    apply existsUnique_of_exists_of_unique
    · simp only [CNF.eval, StateExists, CNF.Clause.eval, List.size_toArray, List.length_cons,
      List.length_nil, zero_add, List.all_toArray', List.all_cons, List.any_map, List.all_nil,
      Bool.and_true, List.any_eq_true, Function.comp_apply, beq_true, Prod.exists,
      List.pair_mem_product, states.complete, true_and] at he
      obtain ⟨s, n, _, _⟩ := he
      use (⟨n, by grind [Int.mem_range_iff]⟩, s)
    · rintro ⟨n₁, s₁⟩ ⟨n₂, s₂⟩ hn₁ hn₂
      simp [CNF.eval, CNF.Clause.eval, StateUnique] at hu
      grind [hs.state_normalized]

lemma assignment_state_exists (a : VarIndex tm → Bool) {Q : ℕ} (hs : IsSuitable a Q) :
    ∀ t, ∃! (pos_state : ℤ × Option tm.State),
      a (VarIndex.state t pos_state.1 pos_state.2) = true := by
  intro t
  wlog ht : t ≤ Q
  · simp [hs.state_eventually_const t (by linarith), this _ hs]
  · have hw := hs.well_defined
    simp only [CNF.Sat, WellDefined, WellDefined₀, List.append_assoc, List.cons_append,
      List.nil_append, CNF.eval_flatten, List.all_map, List.all_eq_true, List.mem_range,
      Order.lt_add_one_iff, Function.comp_apply, List.all_append, List.all_cons, List.all_nil,
      Bool.and_true, Bool.and_eq_true] at hw
    obtain ⟨_, _, he, hu⟩ := hw t ht
    apply existsUnique_of_exists_of_unique
    · simp only [CNF.eval, StateExists, CNF.Clause.eval, List.size_toArray, List.length_cons,
      List.length_nil, zero_add, List.all_toArray', List.all_cons, List.any_map, List.all_nil,
      Bool.and_true, List.any_eq_true, Function.comp_apply, beq_true, Prod.exists,
      List.pair_mem_product, states.complete, true_and] at he
      obtain ⟨s, n, _, _⟩ := he
      use (n, s)
    · rintro ⟨n₁, s₁⟩ ⟨n₂, s₂⟩ hn₁ hn₂
      simp [CNF.eval, CNF.Clause.eval, StateUnique] at hu
      grind [hs.state_normalized]

omit [Fintype Symbol] [DecidableEq Symbol] in
def mkShiftedBiTape (Q : ℕ) (f : ℤ → Option Symbol) (head : ℤ) : BiTape Symbol :=
  BiTape.mk₃ (a := -Q - head) (b := Q + 1 - head) fun n _ ↦ f (n + head)

omit [Fintype Symbol] [DecidableEq Symbol] in
@[simp]
lemma recoverTape_nth {Q : ℕ} (f : ℤ → Option Symbol) (head : ℤ) (n : ℤ) :
    (mkShiftedBiTape Q f head).nth n
    = if n + head ∈ tapeIndices Q then (f (n + head)) else none := by
  simp [mkShiftedBiTape]
  grind [Int.mem_range_iff]

def recoverCfgN (a : VarIndex tm → Bool) {Q : ℕ} (hS : IsSuitable a Q) (t : ℕ) : tm.CfgN :=
  let (n, q) := Exists.choose (assignment_state_exists a hS t)
  {
    state := q
    BiTape := mkShiftedBiTape Q (fun n => Exists.choose (assignment_tape_exists a hS t n)) n
    n := n
  }

lemma recoverCfgN_tape_spec (a : VarIndex tm → Bool) {Q : ℕ} (hS : IsSuitable a Q) (t : ℕ)
    (n : ℤ) (s : Option (Option Symbol)) :
    a (VarIndex.tape t n s) = true ↔ (recoverCfgN a hS t).nth n = s := by
  simp [recoverCfgN, SingleTapeTM.CfgN.nth]
  by_cases hn : n ∈ tapeIndices Q
  · simp [hn, ExistsUnique.choose_eq_iff (assignment_tape_exists a hS t n)]
  · simp [hn, hS.tape_normalized, eq_comm]

lemma recoverCfgN_state_spec (a : VarIndex tm → Bool) {Q : ℕ} (hS : IsSuitable a Q) (t : ℕ)
    (n : ℤ) (s : Option tm.State) :
    a (VarIndex.state t n s) = true
    ↔ (recoverCfgN a hS t).n = n ∧ (recoverCfgN a hS t).state = s := by
  grind [recoverCfgN, ExistsUnique.choose_eq_iff (assignment_state_exists a hS t) (a := (n, s))]

lemma recoverCfgN_SupportedBy (a : VarIndex tm → Bool) (Q : ℕ) (hS : IsSuitable a Q) (t : ℕ) :
    (recoverCfgN a hS t).IsSupportedBy (Set.Icc (-Q) Q) := by
  unfold SingleTapeTM.CfgN.IsSupportedBy
  constructor
  · grind [Int.mem_range_iff, hS.state_normalized,
      recoverCfgN_state_spec a hS t (recoverCfgN a hS t).n (recoverCfgN a hS t).state]
  · simp_rw [← recoverCfgN_tape_spec]
    grind [Int.mem_range_iff, hS.tape_normalized]

/-- Normalize a truth assignment by setting correct dummy values for variables not occurring in the
`TMSAT`.
- See `normalize_IsNormalized` for a proof that this yields a normalized assignment
- See `normalize_TMSAT_iff` for a proof that this assignment is equivalent for TMSAT
-/
def normalize (a : VarIndex tm → Bool) (Q : ℕ) : VarIndex tm → Bool
  | VarIndex.state t n q =>
    if (tapeIndices Q).contains n then
      a (VarIndex.state (min t Q) n q)
      else false
  | VarIndex.tape t n s =>
    if (tapeIndices Q).contains n then
      a (VarIndex.tape (min t Q) n s)
      else s = ␣

omit [DecidableEq Symbol] [DecidableEq tm.State] in
lemma normalize_IsNormalized (a : VarIndex tm → Bool) (Q : ℕ) :
    IsNormalized (normalize a Q) Q where
  state_normalized n hn t q := by simp [normalize, hn]
  tape_normalized n hn t s := by simp [normalize, hn]
  state_eventually_const := by grind [normalize]
  tape_eventually_const := by grind [normalize]

omit [DecidableEq Symbol] [DecidableEq tm.State] in
lemma normalize_Sat_iff (Q : ℕ) (a : VarIndex tm → Bool) (sat : CNF (VarIndex tm))
    (hmem : ∀ v, CNF.VarMem v sat → TMSAT.mem tm Q v) :
    CNF.Sat (normalize a Q) sat ↔ CNF.Sat a sat := by
  simp only [CNF.Sat, Bool.coe_iff_coe]
  apply CNF.eval_congr
  intro v hv
  specialize hmem v hv
  cases v
  all_goals
    dsimp only [TMSAT.mem] at hmem
    simp [normalize, hmem]

@[simp]
lemma normalize_TMSAT_iff (a : VarIndex tm → Bool) (Q C : ℕ) (inst : List Symbol) (accept : Symbol)
    (hQ : inst.length + 1 + C ≤ Q) :
    CNF.Sat (normalize a Q) (TMSAT tm Q C inst accept) ↔ CNF.Sat a (TMSAT tm Q C inst accept) := by
  apply normalize_Sat_iff
  simp [Mem_TMSAT, hQ]

lemma normalize_IsSuitable_of_WellDefined (a : VarIndex tm → Bool) (Q : ℕ)
    (ha : CNF.Sat a (WellDefined tm Q)) :
    IsSuitable (normalize a Q) Q where
  well_defined := by
    refine (normalize_Sat_iff _ _ _ ?_).mpr ha
    apply Mem_WellDefined_aux₀ tm Q
  state_normalized n hn t q := by simp [normalize, hn]
  tape_normalized n hn t s := by simp [normalize, hn]
  state_eventually_const := by grind [normalize]
  tape_eventually_const := by grind [normalize]

def mkAssignment_aux (states : ℕ → SingleTapeTM.CfgN tm) :
    VarIndex tm → Bool
  | VarIndex.state t n q => (states t).n = n && (states t).state = q
  | VarIndex.tape t n s => (states t).BiTape.nth (n - (states t).n) = s

def mkAssignment (inst : List (Option Symbol)) :
    VarIndex tm → Bool :=
  mkAssignment_aux (fun t ↦ (tm.runN t inst))

lemma mkAssignment_aux_WellDefined (states : ℕ → SingleTapeTM.CfgN tm) (Q : ℕ)
    (hs : ∀ t, (states t).n ∈ tapeIndices Q) :
    CNF.Sat (mkAssignment_aux states) (WellDefined tm Q) := by
  simp [WellDefined, CNF.sat_def, WellDefined₀]
  simp [SymbolExists, SymbolUnique, StateExists, StateUnique, CNF.eval, CNF.Clause.eval,
    mkAssignment_aux]
  grind

end
end Cook
end Turing
