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
public import Cslib.Computability.Machines.Turing.SingleTape.Wrappers
public import Mathlib.Data.Int.Range
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Computability.Encoding
public import Std.Sat.CNF

/-!

# Cook-Levin theorem


-/

@[expose] public section

namespace Computation

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


/-- Language of satisfiable SAT formulas -/
def CNFSAT₀ : Language ΓSAT := sorry

/-- Binary encoding of a finite alphabet as bools -/
def encodeAsBool {Γ : Type} [Fintype Γ] : Γ → List Bool := sorry

/-- Language of satisfiable SAT formulas in the boolean alphabet -/
def CNFSAT : Language Bool := { w.flatMap encodeAsBool | w ∈ CNFSAT₀}

/-- Encode a CNF Sat instance with a finite number of variables in the ΓSAT alphabet. -/
def SATEncoding {n : ℕ} : Computability.Encoding (Std.Sat.CNF (Fin n)) ΓSAT := sorry

theorem SATEncoding.correct {n : ℕ} (c : Std.Sat.CNF (Fin n)) :
  (SATEncoding.encode c) ∈ CNFSAT₀ ↔ ¬ Std.Sat.CNF.Unsat c := sorry


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
      obtain ⟨⟨tm⟩, ⟨verifies⟩⟩ := hl

      exact Nonempty.intro {
        f inst := by
          -- TODO: Can we get [DecidableEq tm.State]?
          classical
          let C := verifies.certSizeBound.eval inst.length
          let Q := max (verifies.time.eval inst.length) (inst.length + 1 + C)
          let Sat := Cslib.Turing.Cook.TMSAT₀ tm Q C inst ΓSAT.one
          exact SATEncoding.encode Sat
        f_correct inst := by
          classical
          rw [SATEncoding.correct]
          rw [← Cslib.Turing.Cook.computation_iff_SAT₀ _ _ (by simp) sorry]
          simp_rw [Cslib.Turing.SingleTapeTM.output_ff]
          -- TODO: finish proof here using existing
          -- also probably refactor into own proof
          sorry
        computable := by
          -- This is hard to show, want to use λ-calculus for it
          sorry
      }



end Cook
end Computation
