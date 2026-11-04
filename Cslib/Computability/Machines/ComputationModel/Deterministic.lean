
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
class DeterministicComputer {τ : Type u} {α β : Type} [IOComputationModel τ α β] (t : τ) where
  unique ⦃l a b b'⦄ : (lts t l).UnlabelledTr a b → (lts t l).UnlabelledTr a b' → b = b'

/-- A computaton model is deterministic if all its computers are deterministic. -/
class DeterministicCM (τ : Type u) {α β : Type} [IOComputationModel τ α β] where
  deterministic (t : τ) : DeterministicComputer t

instance {τ : Type u} {α β : Type} [IOComputationModel τ α β] [DeterministicCM τ] (t : τ) :
    DeterministicComputer t := DeterministicCM.deterministic t

namespace Deterministic

variable {τ : Type*} {α β : Type} [IOComputationModel τ α β] {t : τ} {l : α}
variable [DeterministicComputer t]

lemma existsUnique_step (cfg : cfg t l) :
    ∃! cfg', Step t cfg cfg' := by
  by_cases h : Terminal t cfg
  · simp [Step_of_Terminal h]
  · simp_rw [Step_of_nTerminal h]
    apply existsUnique_of_exists_of_unique
    · simpa [Terminal, LTS.IsTerminal.iff_UnlabelledTr] using h
    · apply DeterministicComputer.unique


/-- The unique successor configuration related to `cfg` by the inherited step relation. -/
noncomputable def step (c : cfg t l) : cfg t l :=
  (existsUnique_step c).choose

/-- `Step` relates `c` to `c'` exactly when `step c = c'`. -/
@[simp, scoped grind =]
lemma step_iff {c c' : cfg t l} : Step t c c' ↔ step c = c' := by
  unfold step
  exact (ExistsUnique.choose_eq_iff _).symm

variable (t) in
/-- The configuration reached by running the machine for `n` steps from `c`.
If the machine halts, it will stay at the halting configuration. -/
noncomputable def runFrom (c : cfg t l) (n : ℕ) : IOComputationModel.cfg t l :=
  step^[n] c

/-- The machine eventually halts on `input` with the given `output`. -/
def Computes (l : α) (l' : Option β) : Prop :=
  ∃ u, Halted t (runFrom t (init t l) u) ∧ output (runFrom t (init t l) u) = l'



end Deterministic


end Cslib.ComputationModel
