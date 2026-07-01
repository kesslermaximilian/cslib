module

public import Cslib.Computability.Machines.SingleTapeTuring.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Tactic.Ring

@[expose] public section

def List.combine {α : Type*} (l₁ : List α) (l₂ : List α) : List (Option α) :=
  l₁.map some ++ [none] ++ l₂.map some

namespace Turing
namespace SingleTapeTM

open Computation
open TransitionMachine

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] (tm : SingleTapeTM Symbol)

@[ext]
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

@[simp, grind =]
lemma CfgN.nth_head (c : CfgN tm) : c.nth c.n = c.BiTape.head := by simp [CfgN.nth]


def initCfgN (s : List Symbol) : tm.CfgN := ⟨initCfg tm s, 0⟩

@[simp]
lemma initCfgN_n (s : List Symbol) : (initCfgN tm s).n = 0 := rfl

@[simp]
lemma initCfgN_BiTape (s : List Symbol) : (initCfgN tm s).BiTape = BiTape.mk₁ s := rfl

lemma initCfg_compatible_apply (s : List Symbol) :  (initCfgN tm s).toCfg = initCfg tm s := rfl

open BiTape

lemma posChange_abs_bound (dir : Option Dir) : |posChange dir| ≤ 1 := by
  match dir with
  | none | some Dir.left | some Dir.right => simp [posChange]; try rfl

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


-- Properties of stepN
section CfgN
variable (c : CfgN tm)

/--
Extended transition function of a SingleTapeTM :
We extend the domain to the halt state `Option tm.State` (instead of `tm.State`)
by performing no writes/moves in this state and staying in the halt state.
This is just a convenience function because it allows us more easily to model the extended
execution behaviour of the TM in the SAT instance.
-/
def tr' (tm : SingleTapeTM Symbol) :
    Option tm.State → Option Symbol → SingleTapeTM.Stmt Symbol × Option tm.State
  | none, a => ({symbol := a, movement := none}, none)
  | some s, a => tm.tr s a

lemma stepN.state_update :
    (stepN tm c).state = (tm.tr' c.state c.BiTape.head).snd := by
  obtain ⟨⟨state, _⟩, _⟩ := c
  cases state
  <;> rfl

lemma stepN.pos_update :
    (stepN tm c).n = c.n + posChange (tm.tr' c.state c.BiTape.head).fst.movement := by
  obtain ⟨⟨state, _⟩, _⟩ := c
  cases state
  · rw [stepN, left_eq_add]
    rfl
  · rfl

lemma stepN.BiTape_update :
    (stepN tm c).BiTape
    = (c.BiTape.write (tm.tr' c.state c.BiTape.head).fst.symbol).optionMove
        (tm.tr' c.state c.BiTape.head).fst.movement
       := by
  obtain ⟨⟨state, _⟩, _⟩ := c
  cases state
  <;> rfl

lemma stepN.nth_update (n : ℤ) :
    (stepN tm c).nth n =
      if n = c.n
      then (tm.tr' c.state c.BiTape.head).fst.symbol
      else c.nth n := by
  rw [CfgN.nth, stepN.BiTape_update, optionMove_nth, write_nth, stepN.pos_update]
  ring_nf
  simp [Int.sub_eq_zero]

lemma stepN.pos_bound (c : CfgN tm) (n : ℕ) :
    |c.n - ((tm.stepN)^[n] c).n| ≤ n := by
  induction n generalizing c with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', stepN.pos_update]
      have := posChange_abs_bound
      grind


end CfgN

/-!

# Support of CfgN
As usual, the *support* of a `(c : CfgN)` is the set of indices `n` such that `c.nth n ≠ none`.
Note that this refers to the *tape indices* (i.e. fixed tape positions wrt to the starting
position), **not** to the tape cells relative to the current r/w head.

We prove some lemmata about how the support set changes upon state transitions.

-/

variable {tm} in
def CfgN.TapeIsSupportedBy (c : CfgN tm) (S : Set ℤ) : Prop :=
  ∀ n, n ∉ S → c.nth n = none

variable {tm} in
/-- The set `S` is a support of the state, i.e. all non-default tape indices lie in `S`
  and the r/w head is in `S` as well.

  **Warning** Note that this is slightly different than the notion `Tape.SupportedBy`,
  since this talks about the _tape indices_, not necessarily the indices relative
  to the current r/w head
-/
def CfgN.IsSupportedBy (c : CfgN tm) (S : Set ℤ) : Prop :=
  c.n ∈ S ∧ c.TapeIsSupportedBy S

variable {tm} in
lemma CfgN_TapeIsSupportedBy_iff_BiTape_SupportedBy {c : CfgN tm} {S : Set ℤ} :
    c.TapeIsSupportedBy S ↔ c.BiTape.IsSupportedBy {s - c.n | s ∈ S} := by
  simp only [CfgN.TapeIsSupportedBy, IsSupportedBy, Set.mem_setOf_eq, not_exists, not_and]
  constructor
  · intro hnone n
    grind [hnone (n + c.n)]
  · grind

lemma CfgN_TapeIsSupportedBy_iff_BiTape_SupportedBy' {c : CfgN tm} {S : Set ℤ} (h : c.n = 0) :
    c.TapeIsSupportedBy S ↔ c.BiTape.IsSupportedBy S := by
  simp [CfgN_TapeIsSupportedBy_iff_BiTape_SupportedBy, h]

/-- `SupportedBy` is monotone -/
lemma IsSupportedBy_of_subset {c : CfgN tm} {S S' : Set ℤ} (hS : S ⊆ S') :
    c.IsSupportedBy S → c.IsSupportedBy S' := by
  grind [CfgN.IsSupportedBy, CfgN.TapeIsSupportedBy]

lemma SupportedBy_propagate_Tape (c : CfgN tm) {S : Set ℤ} (h : c.IsSupportedBy S) :
    (stepN tm c).TapeIsSupportedBy S := by
  grind [CfgN.IsSupportedBy, stepN.nth_update, CfgN.TapeIsSupportedBy]

--lemma SupportedBy_propagate_BiTape_Support (c : CfgN tm) (S : Set ℤ) (h : c.IsSupportedBy S) :
--  (stepN tm c).BiTape.IsSupportedBy

lemma IsSupportedBy_propagate (c : CfgN tm) (n : ℕ) {S : Set ℤ} (hS : c.IsSupportedBy S) :
    ((tm.stepN)^[n] c).IsSupportedBy (S ∪ Set.Icc (c.n - n) (c.n + n)) := by
  induction n with
  | zero =>
    exact IsSupportedBy_of_subset tm (by simp) hS
  | succ n ih =>
    constructor
    · grind [stepN.pos_bound tm c (n + 1)]
    · intro n hn
      rw [Function.iterate_succ_apply']
      apply SupportedBy_propagate_Tape tm _ ih
      grind

lemma IsSupportedBy_initCfgN (s : List Symbol) :
    (initCfgN tm s).IsSupportedBy (Set.Icc 0 ↑(s.length - 1)) := by
  simp only [CfgN.IsSupportedBy, initCfgN_n, Set.mem_Icc, Std.le_refl, Nat.cast_nonneg, and_self,
    CfgN_TapeIsSupportedBy_iff_BiTape_SupportedBy', initCfgN_BiTape, true_and]
  refine BiTape.IsSupportedBy_of_subset ?_ (mk₁_IsSupportedBy s)
  grind

lemma IsSupportedBy_run (s : List Symbol) (n : ℕ) :
    (runN tm n s).IsSupportedBy (Set.Icc (-n) ↑(max n (s.length - 1))) := by
  refine IsSupportedBy_of_subset _ ?_ (IsSupportedBy_propagate _ _ n (IsSupportedBy_initCfgN tm s))
  grind [initCfgN]

lemma stepN_update_pos_state_iff (c₁ c₂ : tm.CfgN) {S : Set ℤ} (h : c₁.n ∈ S) :
    (tm.stepN c₁).n = c₂.n ∧ (tm.stepN c₁).state = c₂.state ↔
    ∀ (n : S) (s : Option tm.State) (x : (Option Symbol)),
    c₁.nth n = x → c₁.n = n → c₁.state = s
    → c₂.n = n + posChange (tm.tr' s x).fst.movement ∧ c₂.state = (tm.tr' s x).snd := by
  simp [stepN.state_update, stepN.pos_update]
  grind

lemma foo {S : Set ℤ} (n : ℤ) (P : ℤ → Prop) :
    (∀ x ∈ {s - n | s ∈ S}, P x) ↔ ∀ x ∈ S, P (x - n) := by
  grind

lemma stepN_update_BiTape_iff {c₁ c₂ : tm.CfgN} {S : Set ℤ}
    (hc₁ : c₁.IsSupportedBy S) (hc₂ : c₂.TapeIsSupportedBy S) (hpos : (tm.stepN c₁).n = c₂.n) :
    (tm.stepN c₁).BiTape = c₂.BiTape ↔
    ∀ (n : ℤ) (b : Option Symbol) (s : Option tm.State),
    n ∈ S →
    (¬ c₁.nth n = b ∨ (¬ c₁.n = n ∨ ¬ c₁.state = s)  ∨ c₂.nth n = (tm.tr' s b).1.symbol)
    ∧ ∀ x ∈ S, x = n ∨ (¬ c₁.nth n = b ∨ (¬ c₁.n = x ∨ ¬c₁.state = s) ∨ c₂.nth n = b)
    := by
  have : (∀ n ∈ S, (tm.stepN c₁).nth n = c₂.nth n) ↔ (tm.stepN c₁).BiTape = c₂.BiTape := by
    have hs₁ : (tm.stepN c₁).BiTape.IsSupportedBy {s - c₂.n | s ∈ S} := by
      rw [← hpos, ← CfgN_TapeIsSupportedBy_iff_BiTape_SupportedBy]
      apply SupportedBy_propagate_Tape
      assumption
    have hs₂ : c₂.BiTape.IsSupportedBy {s - c₂.n | s ∈ S} :=
      CfgN_TapeIsSupportedBy_iff_BiTape_SupportedBy.mp hc₂
    simpa [CfgN.nth, hpos] using BiTape.ext_nth_SupportedBy hs₁ hs₂
  simp [← this, stepN.nth_update, ← imp_iff_not_or]
  grind [hc₁.1]

--set_option profiler true
--set_option trace.profiler true

omit [Inhabited Symbol] in
lemma zip_Idx_iff (tm : SingleTapeTM (Option Symbol)) (inst : List Symbol) (c : tm.CfgN) :
    (∀ (s : Symbol) (n : ℕ), (s, n) ∈ inst.zipIdx → c.nth n = some (some s))
    ↔
    (∀ (n : ℤ), 0 ≤ n → n < inst.length → c.nth n = some (inst[n.toNat]?)) := by
  grind

lemma index_partition {Q I C : ℕ} (h : I + 1 + C ≤ Q) :
    Set.Icc (α := ℤ) (-Q) Q
    = Set.Ico (α := ℤ) 0 I
      ∪ Set.Icc (α := ℤ) I I
      ∪ Set.Ico (α := ℤ) (I + 1) (I + C + 1)
      ∪ Set.Ico (α := ℤ) (-Q) 0
      ∪ Set.Icc (I + C + 1) Q := by
  grind

omit [Inhabited Symbol] in
lemma initCfgN_iff (tm : SingleTapeTM (Option Symbol)) (inst : List Symbol) {C Q : ℕ} {c : tm.CfgN}
    (h : inst.length + 1 + C ≤ Q) (hs : c.IsSupportedBy (Set.Icc (-Q) Q)) :
    (∃ cert, cert.length = C ∧ c = tm.initCfgN (List.combine inst cert))
    ↔
    c.n = 0
    ∧ c.state = some tm.q₀
    ∧ (∀ (s : Symbol) (n : ℕ), (s, n) ∈ inst.zipIdx → c.nth n = some (some s))
    ∧ c.nth inst.length = some none
    ∧ (∀ (n : ℤ), inst.length + 1 ≤ n → n < inst.length + C + 1 → (c.nth n).join ≠ none)
    ∧ (∀ (n : ℤ), -↑Q ≤ n ∧ n < 0 ∨ inst.length + C + 1 ≤ n ∧ n < Q + 1 → c.nth n = none)
  := by
  constructor
  · intro ⟨cert, hlen, heq⟩
    simp only [CfgN.ext_iff, initCfgN, initCfg_state, initCfg_BiTape] at heq
    grind [List.combine]
  · rintro ⟨hpos, hstate, hinst, hsep, hcert, hnone⟩
    let indices := Int.range (inst.length + 1) (inst.length + C + 1)
    have : ∀ n, n ∈ indices → (c.nth n ).join.isSome := by
      intro n
      specialize hcert n
      grind [Int.mem_range_iff, Option.ne_none_iff_isSome]
    let cert := indices.pmap (fun n h => (c.nth n).join.get h) this
    have hlen : cert.length = C := by simp [cert, indices, Int.range]
    use cert
    constructor
    · exact hlen
    · rw [CfgN.ext_iff]
      simp only [hstate, initCfgN, initCfg_state, initCfg_BiTape, hpos, and_true, true_and]
      refine (BiTape.ext_nth_SupportedBy (S := Set.Icc (-Q) Q) ?_ ?_).mp ?_
      · rw [← CfgN_TapeIsSupportedBy_iff_BiTape_SupportedBy' _ hpos]
        exact hs.right
      · refine BiTape.IsSupportedBy_of_subset ?_ (mk₁_IsSupportedBy (List.combine inst cert))
        simp [List.combine]
        grind
      · intro n hn
        rw [show c.BiTape.nth n = c.nth n by simp [CfgN.nth, hpos]]
        simp only [index_partition h, Set.mem_union, or_assoc] at hn
        obtain (h | h | h | h | h) := hn
        · rw [zip_Idx_iff] at hinst
          specialize hinst n h.1 h.2
          grind [List.combine]
        · grind [List.combine]
        · specialize hcert n h.1 h.2
          let m := n.toNat
          have : n = m := by grind
          grind [Int.range, List.combine]
        all_goals
          simp [CfgN.nth, hpos] at hnone
          grind [List.combine]

/-
(∃ c, c.length = C ∧ recoverCfgN a Q 0 = tm.initCfgN (inst.combine c)) ↔
  (((((recoverCfgN a Q 0).n = 0 ∧ (recoverCfgN a Q 0).state = some tm.q₀) ∧
          ∀ (a_1 : Symbol) (b : ℕ), (a_1, b) ∈ inst.zipIdx → (recoverCfgN a Q 0).nth ↑b = some (some a_1)) ∧
        (recoverCfgN a Q 0).nth ↑inst.length = some none) ∧
      ∀ (x : ℤ), ↑inst.length + 1 ≤ x → x < ↑inst.length + ↑C + 1 → (recoverCfgN a Q 0).nth x ∈ instanceSymbols) ∧
    ∀ (x : ℤ), -↑Q ≤ x ∧ x < 0 ∨ ↑inst.length + ↑C + 1 ≤ x ∧ x < ↑Q + 1 → (recoverCfgN a Q 0).nth x = none
-/

end SingleTapeTM
end Turing
