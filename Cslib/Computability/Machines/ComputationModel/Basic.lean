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

/-- A configuration type, label type, and labelled transition system for each computer. -/
class ComputationModel (τ : Type u) where
  /-- Configuration type (or state type) associated with a computer -/
  cfg (t : τ) : Type v
  /-- Label type associated with the LTS of a computer -/
  label (t : τ) : Type w
  /-- Resulting LTS of a computer -/
  lts (t : τ) : LTS (cfg t) (label t)

/--
Configurations of (computers of) this `ComputationModel` have a notion of occupied space,
measured in `ℕ`. -/
class SpaceSize (τ : Type u) [ComputationModel τ] where
  space_used {t : τ} : ComputationModel.cfg t → ℕ

/--
Bundles a `ComputationModel` with input and output functions from/to types `α` and `β`.
This way, we can think of elements of `τ` as allowing computations `α → β` by lifting inputs into
the computation context, following labelled transitions and taking output from this computation
context.
-/
class IOComputationModel (τ : Type u) (α β : outParam Type) extends ComputationModel τ
    where
  init {t : τ} : α → cfg t
  output {t : τ} : cfg t → Option β

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

variable {τ : Type u} [ComputationModel τ]

/-- Every execution starting at `a` is finite, for every nondeterministic choice. -/
def HaltsFrom (t : τ) (a : cfg t) : Prop :=
  Relation.SN (lts t).UnlabelledTr a

/-- Every execution prefix starting at `a` contains at most `n` transitions. -/
def HaltsFromInTime (t : τ) (a : cfg t) (n : ℕ) : Prop :=
  ∀ ⦃μs : List (label t)⦄ ⦃b : cfg t⦄, (lts t).MTr a μs b → μs.length ≤ n

variable {t : τ} {a b : cfg t} {n : ℕ}

/-- Universal halting is preserved by reachability. -/
theorem HaltsFrom.of_canReach (h : HaltsFrom t a) (hab : (lts t).CanReach a b) :
    HaltsFrom t b :=
  h.of_rel_reflTransGen ((lts t).reflTransGen_unlabelledTr_iff.mpr hab)

/-- Execution bounds can be increased. -/
theorem HaltsFromInTime.mono : Monotone (HaltsFromInTime t a ·) :=
  fun _ _ hnm h _ _ hex => (h hex).trans hnm

/-- Taking successor state reduces time bound by one. -/
theorem HaltsFromInTime.succ {a b : (cfg t)} {μ : (label t)} (h : HaltsFromInTime t a (n + 1))
    (htr : (lts t).Tr a μ b) : HaltsFromInTime t b n := by
  intro _ _ hmtr
  simpa using h (hmtr.stepL htr)

theorem HaltsFromInTime.haltsFrom (h : HaltsFromInTime t a n) : HaltsFrom t a := by
  induction n generalizing a with
  | zero =>
      apply Relation.SN.of_normal
      intro ⟨_, _, htr⟩
      simpa using h (LTS.MTr.single _ htr)
  | succ n ih =>
      apply Relation.SN.intro
      rintro b ⟨_, htr⟩
      exact ih (HaltsFromInTime.succ h htr)

/-- Halting in time zero is the same as being a terminal configuration -/
theorem haltsFromInTime_zero_iff : HaltsFromInTime t a 0 ↔ (lts t).IsTerminal a := by
  constructor
  · intro h _ _ htr
    simpa using h (LTS.MTr.single _ htr)
  · intro h _ _ hex
    cases hex with
    | refl => simp
    | stepL htr _ => exact (h _ _ htr).elim

/-- Reachability in the computer's labelled transition system. -/
def EvalsTo (t : τ) (a b : cfg t) := LTS.CanReach (lts t) a b

/--
The machine `t` reaches `b` from `a` in at most `n` steps.
-/
def EvalsToInTime (t : τ) (a b : cfg t) (n : ℕ) :=
  LTS.CanReachIn (lts t) a b n

variable {t : τ} {a b c : cfg t} {n n₁ n₂ : ℕ}

lemma EvalsTo.refl : EvalsTo t a a := LTS.CanReach.refl (lts t) a

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

end ComputationModel

namespace IOComputationModel
open ComputationModel

variable {τ : Type*} {α β : Type} [IOComputationModel τ α β]

/--
A valid execution sequence that halts.
-/
structure HaltingRun (t : τ) (l : α) where
  μs : List (label t)
  ss : List (cfg t)
  haltState : (cfg t)
  haltState_halts : (lts t).IsTerminal haltState
  isExecution : LTS.Execution (lts t) (init l) μs haltState ss

/--
A valid execution sequence that halts within time bound `n`.
-/
structure HaltingRunInTime (t : τ) (l : α) (n : ℕ) extends HaltingRun t l where
  lengthBound : μs.length ≤ n

/-- A terminal run whose length and every visited state's space usage respect the bounds. -/
structure HaltingRunInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (n : ℕ) (s : ℕ)
    extends HaltingRunInTime t l n where
  size_bound : ∀ state ∈ ss, SpaceSize.space_used state ≤ s

/-- At least one computation on `l` reaches a terminal configuration. -/
def MayHalt (t : τ) (l : α) : Prop :=
  Nonempty (HaltingRun t l)

/-- Every computation on `l` terminates. No uniform time bound is asserted. -/
def Halts (t : τ) (l : α) : Prop :=
  HaltsFrom t (init l)

/-- Universal halting guarantees that at least one terminal run exists. -/
theorem Halts.mayHalt {t : τ} {l : α} (h : Halts t l) : MayHalt t l := by
  obtain ⟨haltState, hr, hnormal⟩ := h.normalizable
  obtain ⟨μs, hex⟩ := (lts t).reflTransGen_unlabelledTr_iff.mp hr
  obtain ⟨ss, hss⟩ := LTS.Execution.of_mTr hex
  exact Nonempty.intro {
    μs := μs
    ss := ss
    haltState := haltState
    haltState_halts := by
      intro μ c _
      apply hnormal
      use c, μ
    isExecution := hss
  }

/--
Time bounds of `HaltingRunInTime` can be increased.
-/
def HaltingRunInTime.mono {t : τ} {n m : ℕ} {l : α} (hnm : n ≤ m)
    (hv : HaltingRunInTime t l n) : HaltingRunInTime t l m where
  μs := hv.μs
  ss := hv.ss
  haltState := hv.haltState
  haltState_halts := hv.haltState_halts
  isExecution := hv.isExecution
  lengthBound := Nat.le_trans hv.lengthBound hnm

/-- At least one computation terminates within `n` transitions. -/
def MayHaltInTime (t : τ) (l : α) (n : ℕ) : Prop :=
  Nonempty (HaltingRunInTime t l n)

/-- Every computation on `l` terminates within `n` transitions. -/
def HaltsInTime (t : τ) (l : α) (n : ℕ) : Prop :=
  HaltsFromInTime t (init l) n

theorem HaltsInTime.mono {t : τ} {l : α} : Monotone (HaltsInTime t l ·) := by
  exact HaltsFromInTime.mono

/-- A uniform time bound implies universal halting. -/
theorem HaltsInTime.halts {t : τ} {l : α} {n : ℕ} (h : HaltsInTime t l n) :
    Halts t l := h.haltsFrom

/-- A universally bounded computation has a terminal run within the bound. -/
theorem HaltsInTime.mayHaltInTime {t : τ} {l : α} {n : ℕ} (h : HaltsInTime t l n) :
    MayHaltInTime t l n := by
  obtain ⟨run⟩ := h.halts.mayHalt
  exact Nonempty.intro {
    toHaltingRun := run
    lengthBound := h run.isExecution.to_mTr
  }

/-- All execution prefixes respect both the time and space bounds. -/
def HaltsInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (n s : ℕ) : Prop :=
  HaltsInTime t l n ∧ ∀ ⦃μs : List (label t)⦄ ⦃b : cfg t⦄ ⦃ss : List (cfg t)⦄,
    (lts t).Execution (init l) μs b ss → ∀ state ∈ ss, SpaceSize.space_used state ≤ s

/-- Some terminal computation has the specified output, regardless of other branches. -/
def MayOutput (t : τ) (l : α) (l' : Option β) : Prop :=
  ∃ (run : HaltingRun t l), output run.haltState = l'

/-- Some computation produces the specified output within the time bound. -/
def MayOutputInTime (t : τ) (l : α) (l' : Option β) (n : ℕ) : Prop :=
  ∃ (run : HaltingRunInTime t l n), output run.haltState = l'

/-- Some computation produces the specified output within the time and space bounds. -/
def MayOutputInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (l' : Option β)
    (n s : ℕ) : Prop :=
  ∃ (run : HaltingRunInTimeAndSpace t l n s), output run.haltState = l'

/-- All terminal computations agree, without asserting termination of every branch. -/
def OutputUnique (t : τ) (l : α) : Prop :=
  ∀ run₁ run₂ : HaltingRun t l, output run₁.haltState = output run₂.haltState

/-- Every computation terminates, and every terminal computation has output `l'`.
`none` records agreement on absence of an output; use `some b` for a computed value. -/
def Outputs (t : τ) (l : α) (l' : Option β) : Prop :=
  Halts t l ∧ ∀ run : HaltingRun t l, output run.haltState = l'

/-- Every computation terminates within the bound and has the specified output. -/
def OutputsInTime (t : τ) (l : α) (l' : Option β) (n : ℕ) : Prop :=
  HaltsInTime t l n ∧ ∀ run : HaltingRun t l, output run.haltState = l'

/-- All computations respect both bounds and agree on their output. -/
def OutputsInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (l' : Option β)
    (n s : ℕ) : Prop :=
  HaltsInTimeAndSpace t l n s ∧ ∀ run : HaltingRun t l, output run.haltState = l'

/-- The output predicate determines at most one result. -/
theorem Outputs.unique {t : τ} {l : α} {b c : Option β}
    (hb : Outputs t l b) (hc : Outputs t l c) : b = c := by
  obtain ⟨run⟩ := hb.1.mayHalt
  rw [← hb.2 run, hc.2 run]

theorem Outputs.mayOutput {t : τ} {l : α} {b : Option β} (h : Outputs t l b) :
    MayOutput t l b := by
  obtain ⟨run⟩ := h.1.mayHalt
  exact ⟨run, h.2 run⟩

theorem Outputs.outputUnique {t : τ} {l : α} {b : Option β} (h : Outputs t l b) :
    OutputUnique t l :=
  fun run₁ run₂ => (h.2 run₁).trans (h.2 run₂).symm

/-- A computation has an output if and only if it halts and output is unique. -/
theorem exists_outputs_iff {t : τ} {l : α} :
    (∃ b, Outputs t l b) ↔ Halts t l ∧ OutputUnique t l := by
  constructor
  · rintro ⟨b, h⟩
    exact ⟨h.1, h.outputUnique⟩
  · rintro ⟨hhalt, hagree⟩
    obtain ⟨run⟩ := hhalt.mayHalt
    exact ⟨output run.haltState, hhalt, fun run' => hagree run' run⟩

/-- Forgetting a time bound preserves the output. -/
theorem OutputsInTime.outputs {t : τ} {l : α} {b : Option β} {n : ℕ}
    (h : OutputsInTime t l b n) : Outputs t l b := ⟨h.1.halts, h.2⟩

/-- A universal output within a time bound is attained by a run within that bound. -/
theorem OutputsInTime.mayOutputInTime {t : τ} {l : α} {b : Option β} {n : ℕ}
    (h : OutputsInTime t l b n) : MayOutputInTime t l b n := by
  obtain ⟨run⟩ := h.1.mayHaltInTime
  exact ⟨run, h.2 run.toHaltingRun⟩

theorem OutputsInTime.mono {t : τ} {l : α} {l' : Option β} : Monotone (OutputsInTime t l l' · )
    := by
  intro _ _ hnm h
  exact ⟨HaltsInTime.mono hnm h.1, h.2⟩

def ComputesInTime [CompSize α] (t : τ) (f : α → β) (time : ℕ → ℕ) :=
  ∀ (l : α), OutputsInTime t l (some (f l)) (time (compSize l))

def ComputesInPolyTime [CompSize α] (t : τ) (f : α → β) :=
  ∃ (P : Polynomial ℕ), ComputesInTime t f P.eval

/--
"Proof" that `f` is computable by the system `τ`.
A witness machine is bundled as part of this structure,
as well as a function bounding execution time.
-/
structure TimeComputable {Γ Γ' : Type} [CompSize Γ]
    (τ : Type*) [IOComputationModel τ Γ Γ'] (f : Γ → Γ') where
  t : τ
  timeBound : ℕ → ℕ
  outputsFunInTmie : ∀ w, OutputsInTime t w (f w) (timeBound (compSize w))

structure PolyTimeComputable {Γ Γ' : Type} [CompSize Γ]
    (τ : Type*) [IOComputationModel τ Γ Γ'] (f : Γ → Γ') extends TimeComputable τ f where
  poly : Polynomial ℕ
  bounds (n : ℕ) : timeBound n ≤ poly.eval n

end IOComputationModel


namespace AcceptingCM
open IOComputationModel

variable {τ : Type*} {α : Type} [AcceptingCM τ α]

/-- Every branch halts within the bound, and at least one branch accepts. -/
def AcceptsInTime (t : τ) (l : α) (n : ℕ) : Prop :=
  HaltsInTime t l n ∧ MayOutput t l (some true)

/--
Every branch respects both bounds, and at least one branch accepts.
Note that this is _weaker_ than `OutputsInTime t l (some true) n`, since we allow for computations
that reject or fail as well.
-/
def AcceptsInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (n : ℕ) (s : ℕ) : Prop :=
  HaltsInTimeAndSpace t l n s ∧ MayOutput t l (some true)

/-- Every branch halts within the bound and rejects. -/
abbrev RejectsInTime (t : τ) (l : α) (n : ℕ) := OutputsInTime t l (some false) n

/-- Every branch respects both bounds and rejects. -/
abbrev RejectsInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (n : ℕ) (s : ℕ) :=
  OutputsInTimeAndSpace t l (some false) n s

theorem AcceptsInTime.mono {t : τ} {l : α} : Monotone (AcceptsInTime t l · ) :=
  fun _ _ hnm h => ⟨HaltsInTime.mono hnm h.1, h.2⟩

theorem RejectsInTime.mono {t : τ} {l : α} : Monotone (RejectsInTime t l · ) :=
  OutputsInTime.mono

/-- Universal rejection excludes an accepting branch. -/
theorem RejectsInTime.not_acceptsInTime {t : τ} {l : α} {n m : ℕ}
    (h : RejectsInTime t l n) : ¬ AcceptsInTime t l m := by
  rintro ⟨_, run, hout⟩
  simp [h.2 run] at hout

end AcceptingCM


end Computation
