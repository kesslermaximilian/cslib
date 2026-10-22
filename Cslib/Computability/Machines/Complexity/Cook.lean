/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/
module

public import Cslib.Computability.Machines.Turing.SingleTape.Defs
public import Cslib.Computability.Machines.Turing.SingleTape.SatCook
public import Cslib.Computability.Machines.Turing.SingleTape.TMCook
public import Cslib.Computability.Machines.ComputationModel.Equivalence
public import Cslib.Computability.Machines.Turing.SingleTape.SatCook
public import Mathlib.Data.Int.Range
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.DeriveFintype
public import Std.Sat.CNF

/-!

# Cook-Levin theorem


-/

@[expose] public section

namespace Computation

/-- Marks distinguished `accept` and `reject` elements in a type, required to be different. -/
class DenoteAcceptance (Γ : Type*) where
  decidableEq : DecidableEq Γ
  accept : Γ
  reject : Γ
  accept_ne_reject : accept ≠ reject

instance {Γ : Type*} [h : DenoteAcceptance Γ] : DecidableEq Γ :=
  h.decidableEq


instance (Γ : Type*) [DenoteAcceptance Γ] : DenoteAcceptance (Option Γ) where
  decidableEq := inferInstance
  accept := some DenoteAcceptance.accept
  reject := some DenoteAcceptance.reject
  accept_ne_reject := by simp [DenoteAcceptance.accept_ne_reject]

instance (Γ : Type*) [DenoteAcceptance Γ] : DenoteAcceptance (List Γ) where
  decidableEq := inferInstance
  accept := [DenoteAcceptance.accept]
  reject := [DenoteAcceptance.reject]
  accept_ne_reject := by simp [DenoteAcceptance.accept_ne_reject]

def DenoteAcceptance.toBool {Γ : Type*} [DenoteAcceptance Γ] (t : Γ) : Option Bool :=
  if t = DenoteAcceptance.accept then some true
  else if t = DenoteAcceptance.reject then some false
  else none


structure AsAcceptor (τ : Type*) where
  t : τ

instance {Γ Γ' : Type} {τ : Type*} [IOTransitionSystem τ Γ Γ'] [DenoteAcceptance Γ'] :
    IOTransitionSystem (AsAcceptor τ) Γ Bool  where
  cfg a := TransitionSystem.cfg a.t
  red := TransitionSystem.red
  init := InputTransitionSystem.init
  output w := IOTransitionSystem.output w >>= DenoteAcceptance.toBool

/--
Turn a ListTransitionSystem on a sum type into a ListTransitionSystem between the
individual types.
-/
structure WithSplitSum (τ : Type*) where
  t : τ

def extractSnd {A B : Type} (xs : List (A ⊕ B)) : Option (List B) :=
  xs.mapM fun
    | .inl _ => none
    | .inr b => some b

instance {Γ Γ' : Type} (τ : Type*) [ListTransitionSystem τ (Γ ⊕ Γ') (Γ ⊕ Γ')] :
    ListTransitionSystem (WithSplitSum τ) Γ Γ' where
  cfg a := TransitionSystem.cfg a.t
  red := TransitionSystem.red
  init := InputTransitionSystem.init ∘ (List.map Sum.inl)
  output w := (IOTransitionSystem.output w) >>= extractSnd

namespace Cook


inductive ΓSAT where
  | zero
  | one
  | var
  | and
  | or
  | not
  deriving DecidableEq

instance : Fintype ΓSAT := derive_fintype% ΓSAT

instance : Inhabited ΓSAT where
  default := ΓSAT.zero

instance : DenoteAcceptance ΓSAT where
  decidableEq := inferInstance
  accept := ΓSAT.one
  reject := ΓSAT.zero
  accept_ne_reject := ne_of_beq_false rfl


def encodeAsBool {Γ : Type} [Fintype Γ] : Γ → List Bool := sorry

def CNFSAT₀ : Language ΓSAT := sorry

-- SAT as a language, but now in the boolean alphabet
def CNFSAT : Language Bool := { w.flatMap encodeAsBool | w ∈ CNFSAT₀}


-- Example on how we we turn single tape tms into acceptors now
noncomputable example {Γ : Type} [Fintype Γ] [Inhabited Γ] [DenoteAcceptance Γ] :
  AcceptingTransitionSystem (AsAcceptor (Cslib.Turing.SingleTapeTM Γ)) Γ := by
  infer_instance

-- False (but stated here anyway)
theorem SAT₀_P : Computation.DecidableInPolyTime CNFSAT₀
  (AsAcceptor (Cslib.Turing.SingleTapeTM ΓSAT)) := by
    sorry

theorem SAT₀_NP : Computation.VerifiableInPolyTime CNFSAT₀
  (AsAcceptor (Cslib.Turing.SingleTapeTM (Option ΓSAT))) := by
  sorry

theorem SAT₀_NPComplete :
    Computation.IsNPComplete
      CNFSAT₀
      (AsAcceptor (Cslib.Turing.SingleTapeTM (Option ΓSAT)))
      (Cslib.Turing.SingleTapeTM ΓSAT) where
    elemNP := SAT₀_NP
    transforms l hl := by
      obtain ⟨⟨tm⟩, ⟨l', h⟩⟩ := hl




      sorry





end Cook
end Computation
