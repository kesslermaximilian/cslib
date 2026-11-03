/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
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

namespace Computation

open Cslib

open CompSize

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
  Terminal_of_Halted {t : τ} {a : α} {c : cfg t a} : Halted t c → (lts t a).IsTerminal c
  init (t : τ) (a : α) : cfg t a
  output {t : τ} {a : α} : cfg t a → Option β

/--
Configurations of (computers of) this `ComputationModel` have a notion of occupied space,
measured in `ℕ`. -/
class SpaceSize (τ : Type u) [IOComputationModel τ α β] where
  spaceUsed {t : τ} {a : α} : List (IOComputationModel.cfg t a) → ℕ

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


section Executions

variable {τ : Type u} {α β : Type} [IOComputationModel τ α β]

/-- A valid execution sequence in the configuraiton space of this machine with input `l`. -/
structure Run (t : τ) (l : α) where
  μs : List (label t)
  ss : List (cfg t l)
  lastState : (cfg t l)
  isExecution : LTS.Execution (lts t l) (init t l) μs lastState ss

/-- A valid execution sequence that terminates. -/
structure TerminatingRun (t : τ) (l : α) extends Run t l where
  lastState_Terminal : (lts t l).IsTerminal lastState

/-- A valid execution sequence that halts (and in particular, terminates). -/
structure HaltingRun (t : τ) (l : α) extends TerminatingRun t l where
  lastState_halts : Halted t lastState

/-- Construct a halting run from a run whose last state is halted. -/
def HaltingRun.of_Run_Halted {t : τ} {l : α} (run : Run t l) (h : Halted t run.lastState) :
    HaltingRun t l where
  toRun := run
  lastState_halts := h
  lastState_Terminal := Terminal_of_Halted h

structure RunInTime (t : τ) (l : α) (n : ℕ) extends Run t l where
  lengthBound : μs.length ≤ n

structure TerminatingRunInTime (t : τ) (l : α) (n : ℕ)
  extends RunInTime t l n, TerminatingRun t l

/--
A valid execution sequence that halts within time bound `n`.
-/
structure HaltingRunInTime (t : τ) (l : α) (n : ℕ)
  extends TerminatingRunInTime t l n, HaltingRun t l

structure RunInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (n : ℕ) (s : ℕ)
    extends RunInTime t l n where
  spaceBound : SpaceSize.spaceUsed ss ≤ s

structure TerminatingRunInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (n : ℕ) (s : ℕ)
    extends RunInTimeAndSpace t l n s, TerminatingRunInTime t l n

structure HaltingRunInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (n : ℕ) (s : ℕ)
  extends TerminatingRunInTimeAndSpace t l n s, HaltingRunInTime t l n

end Executions

section Halting
variable {τ : Type u} [IOComputationModel τ α β]

/--
A configuration is `Stuck` if it is terminal in the LTS of its machine, i.e. there is no
possilble transition from this state.
-/
def Stuck (t : τ) {l : α} (c : cfg t l) : Prop :=
  (lts t l).IsTerminal c

/-- The one-step relation on configurations. A halted configuration steps only to itself. A running
configuration steps by using any label of the LTS. -/
def Step (t : τ) {l : α} (c c' : cfg t l) : Prop :=
  (lts t l).UnlabelledTr c c' ∨ (Halted t c ∧ c = c')

/-- A halted configuration steps only to itself. -/
lemma Step_of_Halted {t : τ} {l : α} {c c' : cfg t l} (h : Halted t c) :
    Step t c c' ↔ c' = c := by
  have :=  LTS.IsTerminal.iff_UnlabelledTr.mp (Terminal_of_Halted h)
  simp [Step, h, this, eq_comm]

/-- A non-halted configuration steps using the `UnlabelledTr` of the LTS. -/
lemma Step_of_nHalted {t : τ} {l : α} {c c' : cfg t l} (h : ¬ Halted t c) :
    Step t c c' ↔ (lts t l).UnlabelledTr c c' := by
  simp [Step, h]

end Halting
namespace NonDeterministic
variable {τ : Type*} {α β : Type} [IOComputationModel τ α β]

/-- Every execution starting at `a` is finite, for every nondeterministic choice. -/
def TerminatesFrom (t : τ) {l : α} (a : cfg t l) : Prop :=
  Relation.SN (lts t l).UnlabelledTr a

/-- Every execution prefix starting at `a` contains at most `n` transitions. -/
def TerminatesFromInTime (t : τ) {l : α} (a : cfg t l) (n : ℕ) : Prop :=
  ∀ ⦃μs : List (label t)⦄ ⦃b : cfg t l⦄, (lts t l).MTr a μs b → μs.length ≤ n

def TerminatesFromInTimeAndSpace [SpaceSize τ] (t : τ) {l : α} (a : cfg t l) (n : ℕ) (s : ℕ) :=
  ∀ ⦃μs b ss⦄, LTS.Execution (lts t l) a μs b ss → μs.length ≤ n ∧ SpaceSize.spaceUsed ss ≤ s

variable {t : τ} {l : α} {a b : cfg t l} {n : ℕ}

/-- Universal halting is preserved by reachability. -/
theorem TerminatesFrom.of_canRach (h : TerminatesFrom t a) (hab : (lts t l).CanReach a b) :
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
theorem terminatesFromInTime_zero_iff_Stuck : TerminatesFromInTime t a 0 ↔ Stuck t a := by
  constructor
  · intro h _ _ htr
    simpa using h (LTS.MTr.single _ htr)
  · intro h _ _ hex
    cases hex with
    | refl => simp
    | stepL htr _ => exact (h _ _ htr).elim

/-- Reachability in the computer's labelled transition system. -/
def EvalsTo (t : τ) (a b : cfg t l) := LTS.CanReach (lts t l) a b

/--
The machine `t` reaches `b` from `a` in at most `n` steps.
-/
def EvalsToInTime (t : τ) (a b : cfg t l) (n : ℕ) :=
  LTS.CanReachIn (lts t l) a b n

variable {t : τ} {a b c : cfg t l} {n n₁ n₂ : ℕ}

lemma EvalsTo.refl : EvalsTo t a a := LTS.CanReach.refl (lts t l) a

lemma EvalsTo.trans (h₁ : EvalsTo t a b) (h₂ : EvalsTo t b c) : EvalsTo t a c
  := LTS.CanReach.trans h₁ h₂

lemma EvalsToInTime.refl : EvalsToInTime t a a 0 := LTS.CanReachIn.refl _ _

lemma EvalsToInTime.trans (h₁ : EvalsToInTime t a b n₁) (h₂ : EvalsToInTime t b c n₂) :
    EvalsToInTime t a c (n₁ + n₂) := LTS.CanReachIn.trans h₁ h₂

lemma EvalsToInTime.mono : Monotone (EvalsToInTime t a b ·) := LTS.CanReachIn.mono _

/-- A bounded execution also witnesses unbounded reachability. -/
theorem EvalsToInTime.evalsTo (h : EvalsToInTime t a b n) : EvalsTo t a b := h.toCanReach

/- Recover the counted-relation API by forgetting transition labels. -/
--theorem evalsToInTime_iff_relatesWithinSteps :
    --EvalsToInTime t a b n ↔ Relation.RelatesWithinSteps (lts t).UnlabelledTr a b n :=
  --(lts t).relatesWithinSteps_unlabelledTr_iff.symm


variable {τ : Type*} {α β : Type} [IOComputationModel τ α β]


/-- At least one computation on `l` reaches a halting configuration. -/
def MayTerminate (t : τ) (l : α) : Prop :=
  Nonempty (TerminatingRun t l)

/-- Every computation on `l` terminates. No uniform time bound is asserted. -/
def Terminates (t : τ) (l : α) : Prop :=
  TerminatesFrom t (init t l)

def MayHalt (t : τ) (l : α) : Prop :=
  Nonempty (HaltingRun t l)

/-- Every computation on `l` halts. No uniform time bound is asserted. -/
structure Halts (t : τ) (l : α) : Prop where
  terminates : Terminates t l
  notStuck : ∀ (run : TerminatingRun t l), Halted t run.lastState


/-- Universal halting guarantees that at least one terminal run exists. -/
theorem Terminates.mayTerminate {t : τ} {l : α} (h : Terminates t l) : MayTerminate t l := by
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

theorem Halts.mayHalt {t : τ} (l : α) (h : Halts t l) : MayHalt t l := by
  obtain ⟨run⟩ := h.terminates.mayTerminate
  exact Nonempty.intro {run with lastState_halts := h.notStuck run}

/--
Time bounds of `HaltingRunInTime` can be increased.
-/
def HaltingRunInTime.mono {t : τ} {n m : ℕ} {l : α} (hnm : n ≤ m)
    (hv : TerminatingRunInTime t l n) : TerminatingRunInTime t l m where
  μs := hv.μs
  ss := hv.ss
  lastState := hv.lastState
  lastState_Terminal := hv.lastState_Terminal
  isExecution := hv.isExecution
  lengthBound := Nat.le_trans hv.lengthBound hnm

/-- At least one computation terminates within `n` transitions. -/
def MayTerminateInTime (t : τ) (l : α) (n : ℕ) : Prop :=
  Nonempty (TerminatingRunInTime t l n)

/-- Every computation on `l` terminates within `n` transitions. -/
def TerminatesInTime (t : τ) (l : α) (n : ℕ) : Prop :=
  TerminatesFromInTime t (init t l) n

/-- Every computation on `l` halts. No uniform time bound is asserted. -/
def HaltsInTime (t : τ) (l : α) (n : ℕ) : Prop :=
  ∀ run : Run t l, n ≤ run.μs.length → Halted t run.lastState

--lemma HaltsInTime.terminatesInTime {t : τ} {l : α} {n : ℕ} (h : HaltsInTime )

theorem TerminatesInTime.mono {t : τ} {l : α} : Monotone (TerminatesInTime t l ·) := by
  exact TerminatesFromInTime.mono

/-- A uniform time bound implies universal termination. -/
theorem TerminatesInTime.terminates {t : τ} {l : α} {n : ℕ} (h : TerminatesInTime t l n) :
    Terminates t l := h.terminatesFrom

/-- A universally bounded computation has a terminal run within the bound. -/
theorem TerminatesInTime.mayTerminateInTime {t : τ} {l : α} {n : ℕ} (h : TerminatesInTime t l n) :
    MayTerminateInTime t l n := by
  obtain ⟨run⟩ := h.terminates.mayTerminate
  exact Nonempty.intro {
    toTerminatingRun := run
    lengthBound := h run.isExecution.to_mTr
  }

/-- All execution prefixes respect both the time and space bounds. -/
def TerminatesInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (n s : ℕ) : Prop :=
  --TerminatesInTime t l n ∧
  ∀ ⦃μs : List (label t)⦄ ⦃b : cfg t l⦄ ⦃ss : List (cfg t l)⦄,
    (lts t l).Execution (init t l) μs b ss → μs.length ≤ n ∧ SpaceSize.spaceUsed ss ≤ s

lemma TerminatesInTimeAndSpace.terminatesInTime [SpaceSize τ] {t : τ} {l : α} {n s : ℕ}
    (h : TerminatesInTimeAndSpace t l n s) :
    TerminatesInTime t l n := by
  intro μs b hmtr
  obtain ⟨ss, he⟩ := LTS.mTr_iff_execution.mp hmtr
  exact (h he).1


end NonDeterministic

end ComputationModel

end Computation
