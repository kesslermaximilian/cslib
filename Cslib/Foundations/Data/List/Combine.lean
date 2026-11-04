/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Cslib.Init

/-! # Combine two lists using a separator symbol -/

@[expose] public section

variable {Γ : Type} (fst snd fst' snd' : List Γ)

/--
Combine two lists by embedding them into an alphabet with a separator.
This yields an (injective) encoding of `List Γ × List Γ` into `List (Option Γ)`.
-/
def List.combine : List (Option Γ) :=
  fst.map Option.some ++ [none] ++ snd.map Option.some

lemma List.combine_ith_none (i : ℕ) : (fst.combine snd)[i]? = some none ↔ i = fst.length := by
  grind [List.combine]

@[simp]
lemma List.length_combine : (fst.combine snd).length = fst.length + snd.length + 1 := by
  simp [List.combine, Nat.add_assoc]

lemma List.combine_inj : fst.combine snd = fst'.combine snd' → fst = fst' ∧ snd = snd' := by
  intro h
  have lengthEq : fst.length = fst'.length := by
    apply (List.combine_ith_none _ snd' _).mp
    rw [← h]
    exact (List.combine_ith_none _ _ _).mpr rfl
  unfold List.combine at h
  rw [append_eq_append_iff_of_size_eq_left ?_] at h
  · rw [append_cancel_right_eq] at h
    grind [map_inj_right]
  · simp [lengthEq]
