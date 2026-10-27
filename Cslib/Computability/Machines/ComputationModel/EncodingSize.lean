
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

# Encoding size of objects

-/

@[expose] public section

namespace Computation

/- Means that there is a reasonable notion of "size" on input / output. -/
class EncodingSize (Γ : Type) where
  encodingSize : Γ → ℕ

instance (Γ : Type) [EncodingSize Γ] : EncodingSize (Option Γ) where
  encodingSize x := if h : x.isSome then 1 + EncodingSize.encodingSize (x.get h) else 1

instance (Γ : Type) : EncodingSize (List Γ) where
  encodingSize l := l.length

instance (Γ : Type) : EncodingSize (List Γ × List Γ) where
  encodingSize p := p.fst.length + p.snd.length + 1

instance : EncodingSize Unit where
  encodingSize _ := 0

instance : EncodingSize Bool where
  encodingSize _ := 1

end Computation
