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

@[expose] public section

namespace Turing

variable {State : Type*} {Symbol : Type*} {k n : ℕ} (ntm : MultiTapeNTM k Symbol State)

namespace MultiTapeNTM

/--
The one-step relation on _running_ configurations, restricted to a specific action.
A halted configuration does not step.
A running configuration steps by applying any action related to its state and read
symbols by `Tr`.
-/
@[scoped grind =]
def runningStepUsing {input : List Symbol} (ntm : MultiTapeNTM k Symbol State)
    (action : Action k Symbol State) (c₁ c₂ : Cfg k Symbol State input)
  : Prop :=
  match c₁.state with
  | none => False
  | some q => ntm.Tr q c₁.inputSymbol c₁.workTapeSymbols action ∧ c₂ = action.apply c₁
end MultiTapeNTM


namespace MultiTapeNCM

open Cslib.ComputationModel
open Cslib.IOComputationModel
open Cslib

instance : Cslib.IOComputationModel (MultiTapeNTM k Symbol State)
  (List Symbol) (List Symbol) where
  cfg _ input := Cfg k Symbol State input
  label _ := Action k Symbol State
  lts t _ := { Tr c₁ a c₂ := MultiTapeNTM.runningStepUsing t a c₁ c₂ }
  init t l := MultiTapeNTM.initCfg t l
  output c := c.output
  Halted _ _ c := c.state = none
  _Terminal_of_Halted := by
    intro ntm l c hc
    simp [LTS.IsTerminal, MultiTapeNTM.runningStepUsing, hc]

instance : Cslib.SpaceSize (MultiTapeNTM k Symbol State) where
  spaceUsed ss := ∑ i, (Finset.univ.image fun (n : Fin ss.length) ↦ ss[n].workTapePos i).card
  monotone := by sorry

variable {input : List Symbol} {c c₁ c₂ : Cfg k Symbol State input}

@[simp]
lemma Halted_correct : Halted ntm c ↔ Cfg.Halted c := by rfl

lemma Step_correct : Step ntm c₁ c₂ ↔ MultiTapeNTM.Step ntm c₁ c₂ := by
  simp [Step, runStep, LTS.UnlabelledTr, lts, MultiTapeNTM.runningStepUsing, MultiTapeNTM.Step]
  cases h : c₁.state
  · simp [Cfg.Halted, h, eq_comm,]
  · simp [Cfg.Halted, h]
    rfl

-- TODO: To connect these, we need to relate the
-- `RunPath` and `HaltingRunInTime` structures more,
-- in particular how adding the loops makes them slightly different.
-- This is, however, equivalent
lemma RunsInTime_correct : ntm.RunsInTime input n ↔ HaltsInTime ntm input n := by
  constructor
  · intro h

    sorry
  · sorry

end MultiTapeNCM
end Turing
