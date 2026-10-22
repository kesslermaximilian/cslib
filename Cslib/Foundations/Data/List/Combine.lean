/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Cslib.Init

/-! # Combine two lists using a separator symbol -/

@[expose] public section

/-- Combine two lists by embedding them into an amended alphabet with a separator. -/
def List.combine {Γ : Type} (fst : List Γ) (snd : List Γ) : List (Option Γ) :=
  fst.map Option.some ++ [none] ++ snd.map Option.some
