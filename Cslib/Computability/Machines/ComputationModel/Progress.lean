/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Cslib.Computability.Machines.ComputationModel.Basic


/-!

# Computation models (based on LTSs) with Progression property

A computer has the progressing property `ProgressComputer` if there are no stuck states,
i.e. every terminal state is also a halt state (the opposite is always required to be true).
A computation model satisfies `ProgressCM` if all its computers satisfy `ProgressComputer`.


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
class ProgressComputer {τ : Type u} {α β : Type} [IOComputationModel τ α β] (t : τ) where
  exits_of_nHalted ⦃l a⦄ : ¬ Halted t a → ∃ b, (lts t l).UnlabelledTr a b

/-- A computaton model is deterministic if all its computers are deterministic. -/
class ProgressCM (τ : Type u) {α β : Type} [IOComputationModel τ α β] where
  progress (t : τ) : ProgressComputer t


instance (τ : Type u) {α β : Type} [IOComputationModel τ α β] [ProgressCM τ] (t : τ) :
    ProgressComputer t := ProgressCM.progress t

namespace IOComputationModel

variable {τ : Type*} {α β : Type} [IOComputationModel τ α β]
variable {t : τ} {l : α} {c : cfg t l} [ProgressComputer t]

theorem Halted_of_Terminal (h : Terminal t c) : Halted t c := by
  by_contra hnh
  grind [ProgressComputer.exits_of_nHalted hnh, Terminal, LTS.IsTerminal.iff_UnlabelledTr]

theorem Halted_iff_Terminal :
    Halted t c ↔ Terminal t c := ⟨Terminal_of_Halted, Halted_of_Terminal⟩

/-- Convert a terminating run to a halting one by deducing the halting condition. -/
def TerminatingRun.toHaltingRun (run : TerminatingRun t l c) : HaltingRun t l c where
  toTerminatingRun := run
  lastState_halts := Halted_of_Terminal run.lastState_Terminal

-- TODO: Similar conversion for the other run types

/-- `TerminatesFrom` is the same as `HaltsFrom` for a `ProgressComputer`. -/
@[simp]
theorem TerminatesFrom_iff_HaltsFrom (h : TerminatesFrom t c) : HaltsFrom t c where
  terminates := h
  notStuck run := Halted_of_Terminal run.lastState_Terminal

-- TODO: Prove similar simp lemmas about the other predicates involing "Terminates"

end IOComputationModel




end Cslib.ComputationModel
