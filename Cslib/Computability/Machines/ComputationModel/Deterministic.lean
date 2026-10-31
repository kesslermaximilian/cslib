
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

namespace Computation


section Determinism
open ComputationModel
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


end Determinism
