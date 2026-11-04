/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Order.RelSeries
public import Mathlib.Basic.Rel
public import Cslib.Foundations.Relation.RelatesInSteps
public import Cslib.Foundations.Semantics.LTS.Relation
public import Cslib.Foundations.Semantics.LTS.Execution
public import Cslib.Foundations.Relation.Termination
public import Cslib.Computability.Machines.ComputationModel.CompSize


/-! # Computation models based on labelled transition systems

This file develops typeclasses and general derived notions for transition-based
computation models. Common examples for this include Turing machines
(both single/multitape and deterministic/nondeterministic) and WCBV (weak call-by-value λ-calculus).

Computation (between two types) is modelled as a lifting the input into a
computational context (configuration space), then using a (labelled) transition system to "execute"
computation, and among reaching a terminal configuration, projecting onto the output type.

A `IOComputationModel τ α β` will be a type `τ` whose elements `(t : τ)` all behave like
(potentially different) computers between the input type `α` and output type `β`.
In many contexts, `α` and `β` will be `List Γ` for some `(Γ : Type)`, but definitions are stated
in generality here.

Using an `LTS` for the configuration naturally gives rise to both deterministic and
non-deterministic computation models (with deterministic being a property of this `LTS`).
Thus, we state definitions with the nondeterministic case in mind; the deterministic case
can sometimes be simplified.

Transition-based computation models give a natural way of measuring runtime by counting the number
of transitions in the `LTS`.
Additionally, if the configuration state `cfg t` of a computer has a notion of size,
we can also naturally define the space consumption of a computation as the maximum size of any
intermediate state. This is achieved using the `[SpaceSize τ]` class.


## Main declarations

- `ComputationModel`: configuration types, label types, and an LTS for each computer.
- `IOComputationModel`: a computation model with input initialization and partial output.
- `ComputationModel.HaltsFrom`, `ComputationModel.HaltsFromInTime`: universal termination
  from a configuration, optionally with a uniform bound on execution length.
- `IOComputationModel.HaltingRun`, `IOComputationModel.HaltingRunInTime`: reachable
  terminal configurations, optionally with a bound on the number of transitions.
- `IOComputationModel.OutputsInTime`: a universal time bound and agreement on output.
- `IOComputationModel.TimeComputable`, `IOComputationModel.PolyTimeComputable`:
  computers bundled with bounds on the time needed to compute a function.
- `ListCM τ Γᵢ Γₒ`: Abbreviation for `IOComputationModel τ (List Γᵢ Γₒ)`, i.e. a computation model
on lists
- `AcceptingCM τ α`: Abbreviation for `IOComputationModel τ α Bool`, i.e. a computation model that
only outputs accept/reject.
- `ListAcceptingCM τ Γ`: Abbreviation for `IOComputationModel τ (List Γ) Bool`, i.e. a computation
model that acts as an acceptor/rejector of strings.
-/

@[expose] public section

namespace Cslib

open ComputationModel.CompSize

/--
Bundles a `ComputationModel` with input and output functions from/to types `α` and `β`.
This way, we can think of elements of `τ` as allowing computations `α → β` by lifting inputs into
the computation context, following labelled transitions and taking output from this computation
context.
-/
class IOComputationModel (τ : Type u) (α β : outParam Type)
    where
  /-- Configuration type (or state type) associated with a computer -/
  cfg (t : τ) (a : α) : Type v
  /-- Label type associated with the LTS of a computer -/
  label (t : τ) : Type w
  /-- Resulting LTS of a computer -/
  lts (t : τ) (a : α) : LTS (cfg t a) (label t)
  /-- Whether a state is considered halted (computation has deliberately stopped). -/
  Halted (t : τ) {a : α} : cfg t a → Prop
  /-- Halted states may not have success states, i.e. they are terminal (also called `Stuck`). -/
  _Terminal_of_Halted {t : τ} {a : α} {c : cfg t a} : Halted t c → (lts t a).IsTerminal c
  init (t : τ) (a : α) : cfg t a
  output {t : τ} {a : α} : cfg t a → Option β

/--
Configurations of (computers of) this `ComputationModel` have a notion of occupied space,
measured in `ℕ`. -/
class SpaceSize (τ : Type u) [IOComputationModel τ α β] where
  spaceUsed {t : τ} {a : α} : List (IOComputationModel.cfg t a) → ℕ
  monotone {t : τ} {a : α} : ∀ (ss ss' : List (IOComputationModel.cfg t a)),
    ss.IsPrefix ss' → spaceUsed ss ≤ spaceUsed ss'

-- Configuration and label universes are independent and occur together in these aliases.
set_option linter.checkUnivs false in
/-- An `IOComputationModel` between `List Γᵢ` and `List Γₒ`. -/
abbrev ListCM (τ : Type*) (Γᵢ Γₒ : Type) := IOComputationModel τ (List Γᵢ) (List Γₒ)

set_option linter.checkUnivs false in
/-- An `IOComputationModel` between `α` and `Bool`.
`true` and `false` denote acceptance and rejection. -/
abbrev AcceptingCM (τ : Type*) (α : Type) := IOComputationModel τ α Bool

set_option linter.checkUnivs false in
/-- An `IOComputationModel` between `List Γ` and `Bool`.
`true` and `false` denote acceptance and rejection. -/
abbrev ListAcceptingCM (τ : Type*) (Γ : Type) := IOComputationModel τ (List Γ) Bool

namespace ComputationModel
open IOComputationModel

variable {τ : Type u} {α β : Type} [IOComputationModel τ α β]

section Step

/--
A configuration is `Terminal` if it is terminal in the LTS of its machine, i.e. there is no
possible transition from this state.
-/
def Terminal (t : τ) {l : α} (c : cfg t l) : Prop :=
  (lts t l).IsTerminal c

lemma Terminal_iff {t : τ} {l : α} {c : cfg t l} :
    Terminal t c ↔ ∀ c', ¬ (lts t l).UnlabelledTr c c' := by
  simp [Terminal, LTS.IsTerminal.iff_UnlabelledTr]

alias ⟨Terminal.not_UnlabelledTr, Terminal.of_not_UnlabelledTr⟩
  := Terminal_iff

lemma Terminal_of_Halted {t : τ} {a : α} {c : cfg t a} : Halted t c → Terminal t c :=
  _Terminal_of_Halted

/-- A state is stuck if it is terminal but not halted -/
def Stuck (t : τ) {l : α} (c : cfg t l) : Prop :=
  Terminal t c ∧ ¬ Halted t c

/-- The unlabelled version of the LTS, as a relation on configurations. -/
def runStep (t : τ) {l : α} (c c' : cfg t l) : Prop :=
  (lts t l).UnlabelledTr c c'

/-- The one-step relation on configurations. A halted configuration steps only to itself.
A running configuration steps by using any label of the LTS. -/
def Step (t : τ) {l : α} (c c' : cfg t l) : Prop :=
  runStep t c c' ∨ (Halted t c ∧ c = c')

/-- A halted configuration steps only to itself. -/
lemma Step_of_Halted {t : τ} {l : α} {c c' : cfg t l} (h : Halted t c) :
    Step t c c' ↔ c' = c := by
  simp [Step, h, eq_comm, runStep, (Terminal_of_Halted h).not_UnlabelledTr]

/-- A non-halted configuration steps using the `UnlabelledTr` of the LTS. -/
lemma Step_of_nHalted {t : τ} {l : α} {c c' : cfg t l} (h : ¬ Halted t c) :
    Step t c c' ↔ (lts t l).UnlabelledTr c c' := by
  simp [Step, h, runStep]

/-- The one-step relation on configurations for `input`, as a set of pairs. -/
abbrev stepRel (t : τ) (l : α) : SetRel (cfg t l) (cfg t l) :=
  {(c, c') | Step t c c'}

/-- The one-step relation on configurations for `input`, as a set of pairs. -/
abbrev runningStepRel (t : τ) (l : α) : SetRel (cfg t l) (cfg t l) :=
  {(c, c') | ¬ Halted t c ∧ Step t c c'}

-- TODO: This is maybe the more "canonical" definition in the abstract framework?
/-- The one-step relation on configurations for `input`, as a set of pairs. -/
abbrev runningStepRel' (t : τ) (l : α) : SetRel (cfg t l) (cfg t l) :=
  {(c, c') | (lts t l).UnlabelledTr c c'}

example (t : τ) (l : α) :
    runningStepRel t l = runningStepRel' t l := by
  rw [runningStepRel, runningStepRel']
  simp only [Step, Set.ofPred.injEq]
  funext x
  rw [eq_iff_iff]
  constructor
  · grind [runStep]
  · intro h
    simp only [runStep, h, true_or, and_true]
    intro hh
    exact (Terminal_of_Halted hh).not_UnlabelledTr _ h

end Step

section Runs
variable (t : τ) (l : α) (c : cfg t l) (n s : ℕ)

/-- A nonempty list of configurations joined by steps of `t`. -/
abbrev RunPath (t : τ) (l : α) := RelSeries (stepRel t l)

/-- A valid execution sequence in the configuraiton space of this machine with input `l`. -/
structure Run where
  lastState : (cfg t l)
  μs : List (label t)
  ss : List (cfg t l)
  isExecution : LTS.Execution (lts t l) c μs lastState ss

/-- A valid execution sequence that terminates. -/
structure TerminatingRun extends Run t l c where
  lastState_Terminal : (lts t l).IsTerminal lastState

/-- A valid execution sequence that halts (and in particular, terminates). -/
structure HaltingRun extends TerminatingRun t l c where
  lastState_halts : Halted t lastState

variable {t l} in
/-- Construct a halting run from a run whose last state is halted. -/
def HaltingRun.of_Run_Halted (run : Run t l c) (h : Halted t run.lastState) :
    HaltingRun t l c where
  toRun := run
  lastState_halts := h
  lastState_Terminal := Terminal_of_Halted h

structure RunInTime extends Run t l c where
  timeBound : μs.length ≤ n

structure TerminatingRunInTime
  extends RunInTime t l c n, TerminatingRun t l c

/--
A valid execution sequence that halts within time bound `n`.
-/
structure HaltingRunInTime
  extends TerminatingRunInTime t l c n, HaltingRun t l c

variable [SpaceSize τ]

structure RunInTimeAndSpace extends RunInTime t l c n where
  spaceBound : SpaceSize.spaceUsed ss ≤ s

structure TerminatingRunInTimeAndSpace
  extends RunInTimeAndSpace t l c n s, TerminatingRunInTime t l c n

structure HaltingRunInTimeAndSpace
  extends TerminatingRunInTimeAndSpace t l c n s, HaltingRunInTime t l c n

abbrev Computation := Run t l (init t l)
abbrev TerminatingComputation := TerminatingRun t l (init t l)
abbrev HaltingComputation := HaltingRun t l (init t l)
abbrev ComputationInTime := RunInTime t l (init t l) n
abbrev TerminatingComputationInTime := TerminatingRunInTime t l (init t l) n
abbrev HaltingComputationInTime := HaltingRunInTime t l (init t l) n
abbrev ComputationInTimeAndSpace := RunInTimeAndSpace t l (init t l) n s
abbrev TerminatingComputationInTimeAndSpace := TerminatingRunInTimeAndSpace t l (init t l) n s
abbrev HaltingComputationInTimeAndSpace := HaltingRunInTimeAndSpace t l (init t l) n s

/- TODO: Analogue versions of this for the other notions? -/
/--
Time bounds of `TerminatingRunInTime` can be increased.
-/
def TerminatingRunInTime.mono {t : τ} {n m : ℕ} {l : α} (hnm : n ≤ m) {c : cfg t l}
    (hv : TerminatingRunInTime t l c n) : TerminatingRunInTime t l c m where
  lastState := hv.lastState
  μs := hv.μs
  ss := hv.ss
  lastState_Terminal := hv.lastState_Terminal
  isExecution := hv.isExecution
  timeBound := Nat.le_trans hv.timeBound hnm

end Runs


section Reachability

/-- Reachability in the computer's labelled transition system. -/
def EvalsTo {l : α} (t : τ) (a b : cfg t l) := LTS.CanReach (lts t l) a b

/--
The machine `t` reaches `b` from `a` in at most `n` steps.
-/
def EvalsToInTime (t : τ) (a b : cfg t l) (n : ℕ) :=
  LTS.CanReachIn (lts t l) a b n

variable {l : α} {t : τ} {a b c : cfg t l} {n n₁ n₂ : ℕ}

lemma EvalsTo.refl : EvalsTo t a a := LTS.CanReach.refl (lts t l) a

lemma EvalsTo.trans (h₁ : EvalsTo t a b) (h₂ : EvalsTo t b c) : EvalsTo t a c
  := LTS.CanReach.trans h₁ h₂

lemma EvalsToInTime.refl : EvalsToInTime t a a 0 := LTS.CanReachIn.refl _ _

lemma EvalsToInTime.trans (h₁ : EvalsToInTime t a b n₁) (h₂ : EvalsToInTime t b c n₂) :
    EvalsToInTime t a c (n₁ + n₂) := LTS.CanReachIn.trans h₁ h₂

lemma EvalsToInTime.mono : Monotone (EvalsToInTime t a b ·) := LTS.CanReachIn.mono _

/-- A bounded execution also witnesses unbounded reachability. -/
theorem EvalsToInTime.evalsTo (h : EvalsToInTime t a b n) : EvalsTo t a b := h.toCanReach

end Reachability

section Termination

/-- Every execution starting at `a` is finite, for every nondeterministic choice. -/
def TerminatesFrom (t : τ) {l : α} (a : cfg t l) : Prop :=
  Relation.SN (lts t l).UnlabelledTr a

/-- Every execution prefix starting at `a` contains at most `n` transitions. -/
def TerminatesFromInTime (t : τ) {l : α} (a : cfg t l) (n : ℕ) : Prop :=
  ∀ ⦃μs : List (label t)⦄ ⦃b : cfg t l⦄, (lts t l).MTr a μs b → μs.length ≤ n

def TerminatesFromInTimeAndSpace [SpaceSize τ] (t : τ) {l : α} (a : cfg t l) (n : ℕ) (s : ℕ) :=
  ∀ ⦃μs b ss⦄, LTS.Execution (lts t l) a μs b ss → μs.length ≤ n ∧ SpaceSize.spaceUsed ss ≤ s

/-- Every computation on `l` terminates. No uniform time bound is asserted. -/
abbrev Terminates (t : τ) (l : α) : Prop :=
  TerminatesFrom t (init t l)

/-- Every computation on `l` terminates within `n` transitions. -/
abbrev TerminatesInTime (t : τ) (l : α) (n : ℕ) : Prop :=
  TerminatesFromInTime t (init t l) n

abbrev TerminatesInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (n : ℕ) (s : ℕ) : Prop :=
  TerminatesFromInTimeAndSpace t (init t l) n s

variable {t : τ} {l : α} {a b : cfg t l} {n : ℕ}

/-- Universal termination is preserved by reachability. -/
theorem TerminatesFrom.of_canReach (h : TerminatesFrom t a) (hab : (lts t l).CanReach a b) :
    TerminatesFrom t b :=
  h.of_rel_reflTransGen ((lts t l).reflTransGen_unlabelledTr_iff.mpr hab)

/-- Execution bounds can be increased. -/
theorem TerminatesFromInTime.mono : Monotone (TerminatesFromInTime t a ·) :=
  fun _ _ hnm h _ _ hex => (h hex).trans hnm

/-- Taking successor state reduces time bound by one. -/
theorem TerminatesFromInTime.succ {a b : (cfg t l)} {μ : (label t)}
    (h : TerminatesFromInTime t a (n + 1)) (htr : (lts t l).Tr a μ b) :
    TerminatesFromInTime t b n := by
  intro _ _ hmtr
  simpa using h (hmtr.stepL htr)

theorem TerminatesFromInTime.terminatesFrom (h : TerminatesFromInTime t a n) :
  TerminatesFrom t a := by
  induction n generalizing a with
  | zero =>
      apply Relation.SN.of_normal
      intro ⟨_, _, htr⟩
      simpa using h (LTS.MTr.single _ htr)
  | succ n ih =>
      apply Relation.SN.intro
      rintro b ⟨_, htr⟩
      exact ih (TerminatesFromInTime.succ h htr)

theorem TerminatesFromInTimeAndSpace.terminatesFromIntime [SpaceSize τ] {s : ℕ} :
    TerminatesFromInTimeAndSpace t a n s  → TerminatesFromInTime t a n := by
  intro h μs b hmtr
  obtain ⟨ss, he⟩ := LTS.mTr_iff_execution.mp hmtr
  exact (h he).1

/-- Halting in time zero is the same as being a terminal configuration -/
theorem terminatesFromInTime_zero_iff_Stuck : TerminatesFromInTime t a 0 ↔ Terminal t a := by
  constructor
  · intro h _ _ htr
    simpa using h (LTS.MTr.single _ htr)
  · intro h _ _ hex
    cases hex with
    | refl => simp
    | stepL htr _ => exact (h _ _ htr).elim


/-- At least one computation on `l` reaches a halting configuration. -/
def MayTerminateFrom (t : τ) {l : α} (c : cfg t l) : Prop :=
  Nonempty (TerminatingRun t l c)

/-- At least one computation on `l` reaches a halting configuration. -/
def MayTerminate (t : τ) (l : α) : Prop :=
  Nonempty (TerminatingComputation t l)

-- TODO: Could prove more of these equivalence lemmas, but they are rfl anyways?
-- Need to see how often we would use them.
lemma MayTerminate_iff_MayTerminateFrom_init {t : τ} {l : α} :
    MayTerminate t l ↔ MayTerminateFrom t (init t l) := by rfl

/-- At least one computation terminates within `n` transitions. -/
def MayTerminateFromInTime (t : τ) {l : α} (c : cfg t l) (n : ℕ) : Prop :=
  Nonempty (TerminatingRunInTime t l c n)

/-- At least one computation terminates within `n` transitions. -/
def MayTerminateInTime (t : τ) (l : α) (n : ℕ) : Prop :=
  Nonempty (TerminatingComputationInTime t l n)

/-- At least one computation terminates within `n` transitions. -/
def MayTerminateFromInTimeAndSpace [SpaceSize τ] (t : τ) {l : α} (c : cfg t l) (n s : ℕ) : Prop :=
  Nonempty (TerminatingRunInTimeAndSpace t l c n s)

/-- At least one computation terminates within `n` transitions. -/
def MayTerminateInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (n s : ℕ) : Prop :=
  Nonempty (TerminatingComputationInTimeAndSpace t l n s)

/-- Universal halting guarantees that at least one terminal run exists. -/
theorem TerminatesFrom.mayTerminateFrom {t : τ} {l : α} (c : cfg t l) (h : TerminatesFrom t c) :
    MayTerminateFrom t c := by
  obtain ⟨lastState, hr, hnormal⟩ := h.normalizable
  obtain ⟨μs, hex⟩ := (lts t l).reflTransGen_unlabelledTr_iff.mp hr
  obtain ⟨ss, hss⟩ := LTS.Execution.of_mTr hex
  exact Nonempty.intro {
    μs := μs
    ss := ss
    lastState := lastState
    lastState_Terminal := by
      intro μ c _
      apply hnormal
      use c, μ
    isExecution := hss
  }

/--
Universal halting within time `n` guarantees that at least one terminal run within time `n` exists.
-/
theorem TerminatesFromInTime.mayTerminateFromInTime {t : τ} {l : α} {c : cfg t l} {n : ℕ}
  (h : TerminatesFromInTime t c n) :
    MayTerminateFromInTime t c n := by
  obtain ⟨run⟩ := h.terminatesFrom.mayTerminateFrom
  exact Nonempty.intro { run with timeBound := h run.isExecution.to_mTr }

/--
Universal halting within time and space bound guarantees that at least one terminal run with
this time and space bound exists.
-/
theorem TerminatesFromInTimeAndSpace.mayTerminateFromInTimeAndSpace [SpaceSize τ] {t : τ} {l : α}
    {c : cfg t l} {n s : ℕ} (h : TerminatesFromInTimeAndSpace t c n s) :
    MayTerminateFromInTimeAndSpace t c n s := by
  obtain ⟨run⟩ := h.terminatesFromIntime.mayTerminateFromInTime
  exact Nonempty.intro { run with spaceBound := (h run.isExecution).2 }

end Termination


section Halting

/-- Every computation on `l` halts. No uniform time bound is asserted. -/
structure HaltsFrom (t : τ) {l : α} (c : cfg t l) : Prop where
  terminates : TerminatesFrom t c
  notStuck : ∀ (run : TerminatingRun t l c), Halted t run.lastState

/-- Every computation on `l` halts. No uniform time bound is asserted. -/
structure HaltsFromInTime (t : τ) {l : α} (c : cfg t l) (n : ℕ) : Prop where
  terminates : TerminatesFromInTime t c n
  notStuck : ∀ (run : TerminatingRun t l c), Halted t run.lastState

/-- Every computation on `l` halts. No uniform time bound is asserted. -/
structure HaltsFromInTimeAndSpace [SpaceSize τ] (t : τ) {l : α} (c : cfg t l) (n s : ℕ) : Prop where
  terminates : TerminatesFromInTimeAndSpace t c n s
  notStuck : ∀ (run : TerminatingRun t l c), Halted t run.lastState

abbrev Halts (t : τ) (l : α) : Prop
  := HaltsFrom t (init t l)

abbrev HaltsInTime (t : τ) (l : α) (n : ℕ) : Prop
  := HaltsFromInTime t (init t l) n

abbrev HaltsInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (n s : ℕ) : Prop
  := HaltsFromInTimeAndSpace t (init t l) n s

theorem HaltsFromInTime.haltsFrom {t : τ} {l : α} {c : cfg t l} {n : ℕ}
    (h : HaltsFromInTime t c n) :
    HaltsFrom t c where
  terminates := h.terminates.terminatesFrom
  notStuck := h.notStuck

theorem HaltsFromInTimeAndSpace.haltsFromInTime [SpaceSize τ] {t : τ} {l : α} {c : cfg t l}
    {n s : ℕ} (h : HaltsFromInTimeAndSpace t c n s) :
    HaltsFromInTime t c n where
  terminates := h.terminates.terminatesFromIntime
  notStuck := h.notStuck

def MayHaltFrom (t : τ) {l : α} (c : cfg t l) : Prop :=
  Nonempty (HaltingRun t l c)

def MayHalt (t : τ) (l : α) : Prop :=
  Nonempty (HaltingComputation t l)

def MayHaltFromInTime (t : τ) {l : α} (c : cfg t l) (n : ℕ) : Prop :=
  Nonempty (HaltingRunInTime t l c n)

def MayHaltInTime (t : τ) (l : α) (n : ℕ) : Prop :=
  Nonempty (HaltingComputationInTime t l n)

def MayHaltFromInTimeAndSpace [SpaceSize τ] (t : τ) {l : α} (c : cfg t l) (n s : ℕ) : Prop :=
  Nonempty (HaltingRunInTimeAndSpace t l c n s)

def MayHaltInTimeAndspace [SpaceSize τ] (t : τ) (l : α) (n s : ℕ) : Prop :=
  Nonempty (HaltingComputationInTimeAndSpace t l n s)


theorem HaltsFrom.mayHaltFrom {t : τ} {l : α} (c : cfg t l) (h : HaltsFrom t c) :
    MayHaltFrom t c := by
  obtain ⟨run⟩ := h.terminates.mayTerminateFrom
  exact Nonempty.intro {run with lastState_halts := h.notStuck run}

theorem HaltsFromInTime.mayHaltFromInTime {t : τ} {l : α} {c : cfg t l} {n : ℕ}
    (h : HaltsFromInTime t c n) :
    MayHaltFromInTime t c n := by
  obtain ⟨run⟩ :=  h.haltsFrom.mayHaltFrom
  exact Nonempty.intro {run with timeBound := h.terminates run.isExecution.to_mTr }

theorem HaltsFromInTimeAndSpace.mayHaltFromInTimeSpace [SpaceSize τ] {t : τ} {l : α} {c : cfg t l}
    {n s : ℕ} (h : HaltsFromInTimeAndSpace t c n s) :
    MayHaltFromInTimeAndSpace t c n s := by
  obtain ⟨run⟩ :=  h.haltsFromInTime.mayHaltFromInTime
  exact Nonempty.intro {run with spaceBound := (h.terminates run.isExecution).2 }


end Halting

end ComputationModel

end Cslib
