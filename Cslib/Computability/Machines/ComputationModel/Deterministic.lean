/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Cslib.Computability.Machines.ComputationModel.Basic
public import Cslib.Computability.Machines.ComputationModel.Progress


/-!

# Determinitstic Computation models (based on LTSs)

This file defines what a Deterministic `IOComputationModel` is.

It develops specialized definitions to the general notions of `IOComputationModel` and proves
their equivalences.

## Main declarations

- `DeterministicCM τ`: All computers of `τ` are deterministic.
-/

@[expose] public section

namespace Cslib.ComputationModel
open Cslib.IOComputationModel
/--
A computer is deterministic if for every given state, there is at most one possible transition.
-/
class DeterministicComputer {τ : Type u} {α β : Type*} [IOComputationModel τ α β] (t : τ) where
  unique ⦃l a b b'⦄ : (lts t l).UnlabelledTr a b → (lts t l).UnlabelledTr a b' → b = b'

/-- A computaton model is deterministic if all its computers are deterministic. -/
class DeterministicCM (τ : Type u) {α β : Type*} [IOComputationModel τ α β] where
  deterministic (t : τ) : DeterministicComputer t

instance {τ : Type u} {α β : Type*} [IOComputationModel τ α β] [DeterministicCM τ] (t : τ) :
    DeterministicComputer t := DeterministicCM.deterministic t

-- Lemmata that will apply to computation models that are both deterministic and never stuck
section DeterministicProgress

variable {τ : Type*} {α β : Type*} [IOComputationModel τ α β] (t : τ) {l : α}
variable [DeterministicComputer t] [ProgressComputer t]


--noncomputable def tr


lemma existsUnique_step (cfg : cfg t l) :
    ∃! cfg', Step t cfg cfg' := by
  by_cases h : Halted t cfg
  · simp [Step_of_Halted h]
  · simp_rw [Step_of_nHalted h]
    apply existsUnique_of_exists_of_unique
    · rw [Halted_iff_Terminal, Terminal, LTS.IsTerminal.iff_UnlabelledTr] at h
      grind
    · apply DeterministicComputer.unique

/-- The unique successor configuration related to `cfg` by the inherited step relation. -/
noncomputable def step (c : cfg t l) : cfg t l :=
  (existsUnique_step t c).choose

variable {t} in
/-- `Step` relates `c` to `c'` exactly when `step c = c'`. -/
@[simp, scoped grind =]
lemma step_iff {c c' : cfg t l} : Step t c c' ↔ step t c = c' := by
  unfold step
  exact (ExistsUnique.choose_eq_iff _).symm


@[simp]
lemma step_of_halt {c : cfg t l} (h : Halted t c) :
    step t c = c := by
  apply step_iff.mp
  rw [Step_of_Halted h]

/-- The configuration reached by running the machine for `n` steps from `c`.
If the machine halts, it will stay at the halting configuration. -/
noncomputable def runFrom (c : cfg t l) (n : ℕ) : IOComputationModel.cfg t l :=
  (step t)^[n] c

/-- The machine eventually halts on `input` with the given `output`. -/
def Computes (l : α) (l' : Option β) : Prop :=
  ∃ u, Halted t (runFrom t (init t l) u) ∧ output (runFrom t (init t l) u) = l'



end DeterministicProgress


end Cslib.ComputationModel
