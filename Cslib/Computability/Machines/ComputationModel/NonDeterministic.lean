
/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Cslib.Computability.Machines.ComputationModel.Basic


/-!

# Nondeterminitstic Computation models (based on LTSs)


## Main declarations

-/

@[expose] public section

namespace Computation.ComputationModel
open IOComputationModel

/-- Some halting computation has the specified output, regardless of other branches. -/
def MayOutput (t : τ) (l : α) (l' : Option β) : Prop :=
  ∃ (run : HaltingRun t l), output run.lastState = l'

/-- Some computation produces the specified output within the time bound. -/
def MayOutputInTime (t : τ) (l : α) (l' : Option β) (n : ℕ) : Prop :=
  ∃ (run : HaltingRunInTime t l n), output run.lastState = l'

/-- Some computation produces the specified output within the time and space bounds. -/
def MayOutputInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (l' : Option β)
    (n s : ℕ) : Prop :=
  ∃ (run : HaltingRunInTimeAndSpace t l n s), output run.lastState = l'

lemma MayOutputInTime.MayOutput {t : τ} {l : α} {l' : Option β} {n : ℕ} :
    MayOutputInTime t l l' n → MayOutput t l l' := by
  rintro ⟨run, h⟩
  use run.toHaltingRun

lemma MayOutputInTimeAndSpace.MayOutputInTime [SpaceSize τ] {t : τ} {l : α} {l' : Option β} {n : ℕ}
    {s : ℕ} :
    MayOutputInTimeAndSpace t l l' n s → MayOutputInTime t l l' n := by
  rintro ⟨run, h⟩
  use run.toHaltingRunInTime

lemma MayOutputInTimeAndSpace.MayOutput [SpaceSize τ] {t : τ} {l : α} {l' : Option β} {n : ℕ}
    {s : ℕ} :
    MayOutputInTimeAndSpace t l l' n s → MayOutput t l l' := by
  rintro ⟨run, h⟩
  use run.toHaltingRun

lemma MayOutput.exists_MayOutputInTime {t : τ} {l : α} {l' : Option β} :
    MayOutput t l l' → ∃ n, MayOutputInTime t l l' n := by
  rintro ⟨run, h⟩
  use run.μs.length, {run with lengthBound := by rfl}

lemma MayOutputInTime.exists_MayOutputInTimeAndSpace [SpaceSize τ] {t : τ} {l : α} {l' : Option β}
    {n : ℕ} :
    MayOutputInTime t l l' n → ∃ s, MayOutputInTimeAndSpace t l l' n s := by
  rintro ⟨run, h⟩
  use SpaceSize.spaceUsed run.ss, {run with spaceBound := by rfl}

/-- All halting computations agree, without asserting termination of every branch. -/
def OutputUnique (t : τ) (l : α) : Prop :=
  ∀ run₁ run₂ : HaltingRun t l, output run₁.lastState = output run₂.lastState

/-- Every computation terminates, and every halting computation has output `l'`.
`none` records agreement on absence of an output; use `some b` for a computed value. -/
def Outputs (t : τ) (l : α) (l' : Option β) : Prop :=
  Halts t l ∧ ∀ run : HaltingRun t l, output run.lastState = l'

/-- Every computation terminates within the bound and has the specified output. -/
def OutputsInTime (t : τ) (l : α) (l' : Option β) (n : ℕ) : Prop :=
  HaltsInTime t l n ∧ ∀ run : TerminatingRun t l, output run.lastState = l'

/-- All computations respect both bounds and agree on their output. -/
def OutputsInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (l' : Option β)
    (n s : ℕ) : Prop :=
  TerminatesInTimeAndSpace t l n s ∧ ∀ run : TerminatingRun t l, output run.lastState = l'

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
    exact ⟨output run.lastState, hhalt, fun run' => hagree run' run⟩

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
  exact ⟨TerminatesInTime.mono hnm h.1, h.2⟩

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


section AcceptingCM
open IOComputationModel

variable {τ : Type*} {α : Type} [AcceptingCM τ α]

/-- Every branch halts within the bound, and at least one branch accepts. -/
def AcceptsInTime (t : τ) (l : α) (n : ℕ) : Prop :=
  TerminatesInTime t l n ∧ MayOutput t l (some true)

/--
Every branch respects both bounds, and at least one branch accepts.
Note that this is _weaker_ than `OutputsInTime t l (some true) n`, since we allow for computations
that reject or fail as well.
-/
def AcceptsInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (n : ℕ) (s : ℕ) : Prop :=
  TerminatesInTimeAndSpace t l n s ∧ MayOutput t l (some true)

/-- Every branch halts within the bound and rejects. -/
abbrev RejectsInTime (t : τ) (l : α) (n : ℕ) := OutputsInTime t l (some false) n

/-- Every branch respects both bounds and rejects. -/
abbrev RejectsInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (n : ℕ) (s : ℕ) :=
  OutputsInTimeAndSpace t l (some false) n s

theorem AcceptsInTime.mono {t : τ} {l : α} : Monotone (AcceptsInTime t l · ) :=
  fun _ _ hnm h => ⟨TerminatesInTime.mono hnm h.1, h.2⟩

theorem RejectsInTime.mono {t : τ} {l : α} : Monotone (RejectsInTime t l · ) :=
  OutputsInTime.mono

/-- Universal rejection excludes an accepting branch. -/
theorem RejectsInTime.not_acceptsInTime {t : τ} {l : α} {n m : ℕ}
    (h : RejectsInTime t l n) : ¬ AcceptsInTime t l m := by
  rintro ⟨_, run, hout⟩
  simp [h.2 run] at hout

end AcceptingCM
end Computation.ComputationModel
