/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Logic.Function.Iterate
public import Cslib.Foundations.Data.RelatesInSteps
public import Cslib.Computability.Machines.ComputationModel.Basic
public import Mathlib.Computability.Language

/-! test-/

@[expose] public section

namespace Computation
namespace TransitionMachine

/--
Machine `τ'` emulates (i.e. replicates computations) machine `τ` with overhead `time`. -/
def EmulatesInTime (Γ Γ' : Type) {α β : Type*} [TransitionMachine α Γ Γ']
  [TransitionMachine β Γ Γ'] (τ : α) (τ' : β) (time : ℕ → ℕ) :=
  ∀ (l : List Γ), ∀ (l' : List Γ') n,
    OutputsInTime τ n l l' → OutputsInTime τ' (time n) l l'


def ReducibleInTime (Γ Γ' : Type) (α β : Type*) [TransitionMachine α Γ Γ']
    [TransitionMachine β Γ Γ'] (time_class : Set (ℕ → ℕ)) :=
  ∀ (τ : α), ∃ (τ' : β) (time: time_class), EmulatesInTime Γ Γ' τ τ' time


abbrev ModelT := Type -> Type -> Type*

class ComputationModel (M : ModelT) where
  transitionMachine : ∀ Γᵢ Γₒ, TransitionMachine.{u, v} (M Γᵢ Γₒ) Γᵢ Γₒ

instance (M : ModelT) [ComputationModel M] (Γᵢ Γₒ : Type) :
  TransitionMachine (M Γᵢ Γₒ) Γᵢ Γₒ := ComputationModel.transitionMachine Γᵢ Γₒ


def ComputationModel.ReducibleInTime (M M' : ModelT) [ComputationModel M] [ComputationModel M']
  (time_class : Set (ℕ → ℕ)) :=
  ∀ Γ Γ', TransitionMachine.ReducibleInTime Γ Γ' (M Γ Γ') (M' Γ Γ') time_class






/-- "Proof" that the specified tm decides the language `l` in polynomial time. -/
structure DecidesInPolyTime (Γ Γ' : Type) {α : Type*} [TransitionMachine α Γ Γ'] (τ : α)
  (l : Language Γ) where
  /-- A time function bounding execution time dependent on input size. -/
  time : Polynomial ℕ
  outputsFun : ∀ a, OutputsInTime tm (time.eval (R := ℕ) a.length) a (l.IndicatorFun a)

end TransitionMachine
end Computation
