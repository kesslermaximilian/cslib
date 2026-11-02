
/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Cslib.Computability.Machines.ComputationModel.Basic
public import Cslib.Computability.Machines.Turing.MultiTape.Nondeterministic

/-!

# ComputationModel of Multi-Tape Turing machines

-/


namespace Turing

variable {State : Type*} {Symbol : Type} {k : ℕ}

namespace MultiTapeNTM

/--
The one-step relation on _running_ configurations.A halted configuration does not step.
A running configuration steps by applying any action related to its state and read
symbols by `Tr`.
-/
@[scoped grind =]
def runningStep (ntm : MultiTapeNTM k Symbol State) (c₁ c₂ : Cfg k Symbol State input) : Prop :=
  match c₁.state with
  | none => False
  | some q =>
    ∃ action, ntm.Tr q c₁.inputSymbol c₁.workTapeSymbols action ∧ c₂ = action.apply c₁
end MultiTapeNTM


namespace MultiTapeNCM

open Computation
open Computation.ComputationModel
open Computation.IOComputationModel



instance [DecidableEq Symbol] : Computation.IOComputationModel (MultiTapeNTM k Symbol State)
  (List Symbol) (List Symbol) where
  cfg t := Σ input, Cfg k Symbol State input
  label t := Unit
  lts t := {
    Tr c₁ _ c₂ := if h : c₁.1 = c₂.1 then MultiTapeNTM.runningStep t c₁.2 (by
      rw [h]
      exact c₂.2
      )
      else False
    }
  init t l := ⟨l, MultiTapeNTM.initCfg t l⟩
  output c := c.2.output




end MultiTapeNCM
end Turing
