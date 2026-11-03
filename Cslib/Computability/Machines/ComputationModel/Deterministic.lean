
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

namespace Cslib.ComputationModel
open IOComputationModel

/--
A computer is deterministic if for every given state, there is at most one possible transition.
Additionally, we require that there is no stuck states, i.e. every non-halted state has a
transition.
-/
class DeterministicComputer {τ : Type u} {α β : Type} [IOComputationModel τ α β] (t : τ) where
  unique ⦃l a b b'⦄ : (lts t l).UnlabelledTr a b → (lts t l).UnlabelledTr a b' → b = b'
  exits_of_nHalted ⦃l a⦄: ¬ Halted t a → ∃ b, (lts t l).UnlabelledTr a b

/-- A computaton model is deterministic if all its computers are deterministic. -/
class DeterministicCM (τ : Type u) {α β : Type} [IOComputationModel τ α β] where
  deterministic (t : τ) : DeterministicComputer t

namespace Deterministic

variable {τ : Type*} {α β : Type} [IOComputationModel τ α β] [d : DeterministicCM τ] {t : τ} {l : α}

lemma existsUnique_step (cfg : cfg t l) :
    ∃! cfg', Step t cfg cfg' := by
  by_cases h : Halted t cfg
  · simp [Step_of_Halted h]
  · simp_rw [Step_of_nHalted h]
    apply existsUnique_of_exists_of_unique
    · exact (d.deterministic t).exits_of_nHalted h
    · apply (d.deterministic t).unique


/-- The unique successor configuration related to `cfg` by the inherited step relation. -/
noncomputable def step {t : τ} (c : cfg t l) : cfg t l :=
  (existsUnique_step c).choose

/-- `Step` relates `c` to `c'` exactly when `step c = c'`. -/
@[simp, scoped grind =]
lemma step_iff {c c' : cfg t l} : Step t c c' ↔ step c = c' := by
  unfold step
  exact (ExistsUnique.choose_eq_iff _).symm

/-- The configuration reached by running the machine for `n` steps from `c`.
If the machine halts, it will stay at the halting configuration. -/
noncomputable def runFrom (t : τ) (c : cfg t l) (n : ℕ) : IOComputationModel.cfg t l :=
  step^[n] c

/-- The machine eventually halts on `input` with the given `output`. -/
def Computes {t : τ} (l : α) (l' : Option β) : Prop :=
  ∃ u, Halted t (runFrom t (init t l) u) ∧ output (runFrom t (init t l) u) = l'



end Deterministic


end Cslib.ComputationModel
