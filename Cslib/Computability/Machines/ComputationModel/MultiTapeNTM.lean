
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

variable {State : Type*} {Symbol : Type} {k : ℕ} (ntm : MultiTapeNTM k Symbol State)

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

open Computation
open Computation.ComputationModel
open Computation.IOComputationModel
open Cslib


instance : Computation.IOComputationModel (MultiTapeNTM k Symbol State)
  (List Symbol) (List Symbol) where
  cfg _ input := Cfg k Symbol State input
  label _ := Action k Symbol State
  lts t _ := { Tr c₁ a c₂ := MultiTapeNTM.runningStepUsing t a c₁ c₂ }
  init t l := MultiTapeNTM.initCfg t l
  output c := c.output


variable {input : List Symbol} {c c₁ c₂ : Cfg k Symbol State input}

--lemma UnlabelledTr : (lts ntm input).UnlabelledTr = --MultiTapeNTM.runningStepUsing

lemma Halted_correct : Stuck ntm c ↔ Cfg.Halted c := by
  rw [Stuck, LTS.IsTerminal, lts, Cfg.Halted]
  constructor
  · intro h
    cases c.state with
    | none => rfl
    | some q =>
      exfalso
      --specialize h (ntm.Tr q c.inputSymbol c.workTapeSymbols )

      sorry
  · sorry

lemma Step_correct : Step ntm c₁ c₂ ↔ MultiTapeNTM.Step ntm c₁ c₂ := by
  --by_cases h : Halted ntm c₁
  simp [Step, LTS.UnlabelledTr, lts, MultiTapeNTM.runningStepUsing, MultiTapeNTM.Step]

  cases c₁.state
  · simp
    sorry
  · simp
    sorry


end MultiTapeNCM
end Turing
