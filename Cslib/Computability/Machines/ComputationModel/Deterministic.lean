
/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Cslib.Computability.Machines.ComputationModel.Basic


/-!

# Determinitstic Computation models (based on LTSs)

This file defines what a Deterministic `IOComputationModel` is.

It develops specialized definitions to the general notions of `IOComputationModel` and proves
their equivalences.

## Main declarations

- `DeterministicCM τ`: All computers of `τ` are deterministic.
-/

@[expose] public section

namespace Computation.ComputationModel
open IOComputationModel

/--
A computer is deterministic if for every given state, there is at least one reachable state.
Note that this is different than `(lts t).Deterministic`, since we require a unique reachable state
regardless of label.
-/
def DeterministicComputer {τ : Type u} [ComputationModel τ] (t : τ) :=
  ∀ ⦃a b b' : cfg t⦄, (lts t).UnlabelledTr a b → (lts t).UnlabelledTr a b' → b = b'

/-- A computaton model is deterministic if all its computers are deterministic. -/
class DeterministicCM (τ : Type u) [ComputationModel τ] where
  deterministic (t : τ) : DeterministicComputer t

namespace Deterministic

variable {τ : Type*} {α β : Type} [IOComputationModel τ α β] [DeterministicCM τ] {t : τ}

lemma existsUnique_step (cfg : cfg t) :
    ∃! cfg', Step cfg cfg' := by
  by_cases h : Halted cfg
  · simp [step_of_halt h]
  · simp_rw [step_of_nHalt h]
    apply existsUnique_of_exists_of_unique
    · simpa [Halted, Cslib.LTS.IsTerminal.iff_UnlabelledTr] using h
    · grind [DeterministicComputer, DeterministicCM.deterministic t]

/-- The unique successor configuration related to `cfg` by the inherited step relation. -/
noncomputable def step {t : τ} (c : cfg t) : cfg t :=
  (existsUnique_step c).choose

/-- `Step` relates `c` to `c'` exactly when `step c = c'`. -/
@[simp, scoped grind =]
lemma step_iff {c c' : cfg t} : Step c c' ↔ step c = c' := by
  unfold step
  exact (ExistsUnique.choose_eq_iff _).symm

/-- The configuration reached by running the machine for `n` steps from `c`.
If the machine halts, it will stay at the halting configuration. -/
noncomputable def runFrom (t : τ) (c : cfg t) (n : ℕ) : ComputationModel.cfg t :=
  step^[n] c

/-- The machine eventually halts on `input` with the given `output`. -/
def Computes {t : τ} (l : α) (l' : Option β) : Prop :=
  ∃ u, Halted (runFrom t (init l) u) ∧ output (runFrom t (init l) u) = l'



end Deterministic


end Computation.ComputationModel
