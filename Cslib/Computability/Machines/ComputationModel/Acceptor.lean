/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Cslib.Computability.Machines.ComputationModel.Basic

/-!

# test

-/

@[expose] public section

namespace Computation

/-- An accepting system with word inputs is an automata acceptor. -/
instance {τ : Type*} {Γ : Type} [AcceptingCM τ (List Γ)] :
    Cslib.Automata.Acceptor τ Γ where
  Accepts t l := IOComputationModel.Outputs t l (some true)


end Computation
