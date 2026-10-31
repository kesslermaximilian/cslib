
/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Logic.Function.Iterate
public import Cslib.Foundations.Relation.RelatesInSteps
public import Cslib.Computability.Automata.Acceptors.Acceptor

/-!

#  size of objects

-/

@[expose] public section

namespace Computation

/- Means that there is a reasonable notion of "size" on input / output. -/
class CompSize (Γ : Type) where
  compSize : Γ → ℕ

instance (Γ : Type) [CompSize Γ] : CompSize (Option Γ) where
  compSize x := if h : x.isSome then 1 + CompSize.compSize (x.get h) else 1

instance (Γ : Type) : CompSize (List Γ) where
  compSize l := l.length

instance (Γ : Type) : CompSize (List Γ × List Γ) where
  compSize p := p.fst.length + p.snd.length + 1

instance : CompSize Unit where
  compSize _ := 0

instance : CompSize Bool where
  compSize _ := 1

end Computation
