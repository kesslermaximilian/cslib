module

public import Cslib.Computability.Machines.SingleTapeTuring.Basic
public import Mathlib.Data.Nat.Find

namespace Turing
namespace SingleTapeTM

open Computation
open TransitionMachine

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] (tm : SingleTapeTM Symbol)


structure CfgN : Type extends Cfg tm where
  /-- Tape position of the r/w head relative to the starting state.
  If this is positive, the initial "center" of the tape is to the left of the current head -/
  n : ℤ
deriving Inhabited

variable {tm} in
/-- Gives the symbol of the tape at _tape index_ `n`.
Remembering the position of the tape head gives us a notion of talking about _tape indices_,
i.e. numebering the positions on the tape with the integers `ℤ`, and thinking of the r/w
head moving, instead of the tape being shiftet and the r/w head being fixed.
That is, tape index `0` will always refer to the cell on the tape where the r/w head started in.

**Warning**: Note that this is different than the symbol that is positioned `n` to the right of
the head: The _tape index_ is invariant with respect to the r/w head moving. -/
abbrev CfgN.nth (c : CfgN tm) (n : ℤ) : Option Symbol := c.BiTape.nth (n - c.n)

variable {tm} in
/-- The set `S` is a support of the state, i.e. all non-default tape indices lie in `S`
  and the r/w head is in `S` as well.

  **Warning** Note that this is slightly different than the notion `Tape.SupportedBy`,
  since this talks about the _tape indices_, not necessarily the indices relative
  to the current r/w head
-/
def IsSupportedBy (c : CfgN tm) (S : Set ℤ) : Prop :=
  c.n ∈ S ∧ ∀ n, n ∉ S → c.nth n = default

def initCfgN (s : List Symbol) : tm.CfgN := ⟨initCfg tm s, 0⟩

lemma initCfg_compatible_apply (s : List Symbol) :  (initCfgN tm s).toCfg = initCfg tm s := rfl

def posChange : Option Dir → ℤ
  | some .left => -1
  | some .right => 1
  | none => 0

def stepN : tm.CfgN → tm.CfgN
  | ⟨⟨none, t⟩, n⟩ =>
    -- If in the halting state, we *maintain* the current configuration
    ⟨⟨none, t⟩, n⟩
  | ⟨⟨some q', t⟩, n⟩ =>
    -- If in state q', perform look up in the transition function
    match tm.tr q' t.head with
    -- and enter a new configuration with state q'' (or none for halting)
    -- and tape updated according to the Stmt
    -- `n` is updated according to the direction of the Stmt
    | ⟨⟨wr, dir⟩, q''⟩ => ⟨⟨q'', (t.write wr).optionMove dir⟩, n + posChange dir⟩

theorem step.compatible (c : CfgN tm) (h : c.state ≠ none) :
    some (tm.stepN c).toCfg = step tm c.toCfg := by
  simp [stepN, step]
  grind

theorem stepN.fixed (c : CfgN tm) (h : c.state = none) :
    tm.stepN c = c := by
  unfold stepN
  grind

theorem stepN.fixed_iterate_apply (c : CfgN tm) (n : ℕ) (h : c.state = none) :
    tm.stepN^[n] c = c := by
  apply Function.iterate_fixed
  apply stepN.fixed
  assumption

theorem step.compatible_apply_iterate_aux (c : CfgN tm) (n : ℕ)
    (hc : ((flip bind tm.step)^[n + 1] c.toCfg) ≠ none ∨ (tm.stepN^[n] c).state ≠ none) :
    some (tm.stepN^[n + 1] c).toCfg = (flip bind tm.step)^[n + 1] (some c.toCfg) := by
  revert hc
  induction n generalizing c with
  | zero =>
    by_cases h : c.state = none
    · simp [h, flip, step.eq_none_iff]
    · simp [step.compatible _ _ h, flip]
  | succ n ih =>
    by_cases h : c.state = none
    · simp [flip, (step.eq_none_iff _ c.toCfg).mpr h, Function.iterate_fixed,
        stepN.fixed_iterate_apply _ _ _ h, h]
    · repeat rw [Function.iterate_succ_apply _ _ (some c.toCfg)]
      rw [flip, Option.bind_eq_bind, Option.bind_some, ← step.compatible _ _ h]
      exact ih (tm.stepN c)

theorem step.compatible_apply_iterate (c : CfgN tm) (n : ℕ)
    (h : ((flip bind tm.step)^[n] c.toCfg) ≠ none) :
    some (tm.stepN^[n] c).toCfg = (flip bind tm.step)^[n] c.toCfg := by
  cases n with
  | zero => rfl
  | succ n =>
    apply step.compatible_apply_iterate_aux
    exact Or.inl h

theorem step.compatible_apply_iterate' (c : CfgN tm) (n : ℕ)
    (h : (tm.stepN^[n] c).state ≠ none) :
    some (tm.stepN^[n + 1] c).toCfg = (flip bind tm.step)^[n + 1] (some c.toCfg) := by
  apply step.compatible_apply_iterate_aux
  exact Or.inr h

def runN (n : ℕ) (s : List Symbol) : CfgN tm :=
  (stepN tm)^[n] (initCfgN tm s)

@[simp]
lemma runN_zero (s : List Symbol) :
    tm.runN 0 s = tm.initCfgN s := rfl

def OutputsInTimeN (n : ℕ) (s s' : List Symbol) :=
  (runN tm n s).state = none ∧ extractOutput (runN tm n s).toCfg = s'

theorem output_iff_aux₁ (s s' : List Symbol) (n : ℕ) :
    Nonempty (OutputsInTime tm n s s') → OutputsInTimeN tm n s s' := by
  intro ⟨hout⟩
  -- Let `m ≤ n` be the number of execution steps
  obtain ⟨m, hm, hr⟩ := hout.evals_to
  obtain ⟨k, hn⟩ := Nat.exists_eq_add_of_le' hm
  have hrm : (tm.stepN^[m] (tm.initCfgN s)).toCfg = tm.haltCfg s' := by
    rw [red_eq_TransitionRelation, init_eq_initCfg, OutputsInTime.haltState_eq_haltCfg,
      TransitionRelation.eq_lambda, Relation.RelatesInSteps.function_Option_iff tm.step,
      ← initCfg_compatible_apply, ← step.compatible_apply_iterate, Option.some_inj] at hr
    · assumption
    · rw [hr]
      apply Option.some_ne_none
  have hrn : (tm.stepN^[n] (tm.initCfgN s)).toCfg = tm.haltCfg s' := by
    rw [hn, Function.iterate_add_apply, stepN.fixed_iterate_apply _ _ k (by rw [hrm]; rfl), hrm]
  simp [OutputsInTimeN, runN, hrn]

theorem output_iff_aux₂ (s s' : List Symbol) (n : ℕ) :
    OutputsInTimeN tm n s s' → Nonempty (OutputsInTime tm n s s') := by
  intro ⟨hstop, hout⟩
  apply Nonempty.intro
  apply OutputsInTime.of_RelatesInSteps
  have hnone : ∃ m, (tm.runN m s).state = none := ⟨n, hstop⟩
  have hle : Nat.find hnone ≤ n := Nat.find_min' _ hstop
  refine ⟨Nat.find hnone, hle, ?_⟩
  rw [TransitionRelation.eq_lambda, Relation.RelatesInSteps.function_Option_iff tm.step,
    ← initCfg_compatible_apply, ← step.compatible_apply_iterate]
  · obtain ⟨k, hn⟩ := Nat.exists_eq_add_of_le' hle
    rw [← stepN.fixed_iterate_apply tm (tm.stepN^[Nat.find hnone] (tm.initCfgN s)) k]
    · rw [← Function.iterate_add_apply, ← hn, ← runN, haltCfg_of_extractOutput hout]
    · exact Nat.find_spec hnone
  · have hne0 : Nat.find hnone ≠ 0 := by
      intro h
      simpa [h, initCfgN] using Nat.find_spec hnone
    rw [← Nat.succ_pred_eq_of_ne_zero hne0, ← step.compatible_apply_iterate']
    · apply Option.some_ne_none
    · exact (Nat.find_min hnone (Nat.sub_one_lt hne0))

theorem output_ff (s s' : List Symbol) (n : ℕ) :
    OutputsInTimeN tm n s s' ↔ Nonempty (OutputsInTime tm n s s') :=
  ⟨output_iff_aux₂ _ _ _ _, output_iff_aux₁ _ _ _ _⟩

end SingleTapeTM
end Turing
