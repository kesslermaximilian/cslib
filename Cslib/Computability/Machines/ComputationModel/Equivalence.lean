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
public import Cslib.Computability.Automata.Acceptors.Acceptor

/-! test-/

@[expose] public section


namespace Computation
namespace IOTransitionSystem
open Cslib.Automata
open IOTransitionSystem

/--
Machine `τ'` emulates (i.e. replicates computations) machine `τ` with overhead `time`. -/
def EmulatesInTime (Γ Γ' : Type) {α β : Type*} [IOTransitionSystem α Γ Γ']
  [IOTransitionSystem β Γ Γ'] (τ : α) (τ' : β) (time : ℕ → ℕ) :=
  ∀ (l : Γ), ∀ (l' : Part Γ') n,
    OutputsInTime τ l l' n → OutputsInTime τ' l l' (time n)

/--
An IOTransitionSystem on `α` is reducible to `β` (in a specified time class),
if all transducers in `α` have an emulator in `β` with time overhead given by a function
of the specified time class.
-/
def ReducibleInTime {Γ Γ' : Type} (α β : Type*) [IOTransitionSystem α Γ Γ']
    [B : IOTransitionSystem β Γ Γ'] (time_class : Set (ℕ → ℕ)) :=
  ∀ (τ : α), ∃ (τ' : β) (time: time_class), EmulatesInTime Γ Γ' τ τ' time

end IOTransitionSystem

abbrev FunctionModelT := Type -> Type -> Type*

class ComputationModel (M : FunctionModelT) (InType : outParam (Type -> Type))
    (OutType : outParam (Type -> Type)) where
  transitionSystem: ∀ Γ Γ', IOTransitionSystem.{u, v} (M Γ Γ') (InType Γ) (OutType Γ')

abbrev FunctionComputationModel (M : FunctionModelT) :=
  ComputationModel M List List

abbrev LanguageRecognitionModel (M : FunctionModelT) :=
  ComputationModel M List (fun _ => Unit)

namespace ComputationModel


-- General instance exposing the typeclass synthesis
instance (M : FunctionModelT) (InType OutType : Type -> Type) [ComputationModel M InType OutType]
    (Γ Γ' : Type): IOTransitionSystem (M Γ Γ') (InType Γ) (OutType Γ') :=
  ComputationModel.transitionSystem Γ Γ'

-- Duplicate, not needed, but here for checking
instance (M : FunctionModelT) [FunctionComputationModel M] (Γ Γ' : Type) :
    ListTransitionSystem (M Γ Γ') Γ Γ' := by
  infer_instance

-- Duplicate, not needed, but here for checking
instance (M : FunctionModelT) [LanguageRecognitionModel M] (Γ : Type) :
    AcceptingTransitionSystem (M Γ Unit) Γ := by
  infer_instance

def ReducibleInTime (M M' : FunctionModelT) {InType OutType}
    [ComputationModel M InType OutType] [ComputationModel M' InType OutType]
    (time_class : Set (ℕ → ℕ)) :=
  ∀ Γ Γ', IOTransitionSystem.ReducibleInTime (M Γ Γ') (M' Γ Γ') time_class

def EquivalentInTime (M M' : FunctionModelT) {InType OutType}
    [ComputationModel M InType OutType] [ComputationModel M' InType OutType]
    (time_class : Set (ℕ → ℕ)) :=
  ReducibleInTime M M' time_class ∧ ReducibleInTime M' M time_class


def NaturalPolynomials : Set (ℕ → ℕ) := { f | ∃ (P : Polynomial ℕ), f = P.eval}

abbrev ReducibleInPolyTime (M M' : FunctionModelT) {InType OutType}
    [ComputationModel M InType OutType] [ComputationModel M' InType OutType] :=
    ReducibleInTime M M' NaturalPolynomials

abbrev EquivalentInPolyTime (M M' : FunctionModelT) {InType OutType}
    [ComputationModel M InType OutType] [ComputationModel M' InType OutType] :=
  EquivalentInTime M M' NaturalPolynomials


end ComputationModel

namespace AcceptingTransitionSystem

open AcceptingTransitionSystem

/-- "Proof" that the specified tm decides the language `l` in polynomial time. -/
structure DecidesInPolyTime {Γ : Type} {τ : Type*} [AcceptingTransitionSystem τ Γ] (t : τ)
  (l : Language Γ) where
  /-- A time function bounding execution time dependent on input size. -/
  time : Polynomial ℕ
  outputsFun : ∀ a, DecidesInTime t a (a ∈ l) (time.eval (R := ℕ) a.length)


def PolyTimeDecidableLanguages (Γ : Type) (M : FunctionModelT) [LanguageRecognitionModel M] :
    Set (Language Γ) :=
  { l | ∃ (t : M Γ Unit), Nonempty (DecidesInPolyTime t l) }

theorem P_constant_aux (M M' : FunctionModelT) [LanguageRecognitionModel M]
    [LanguageRecognitionModel M'] (h : ComputationModel.ReducibleInPolyTime M M') (Γ : Type) :
    PolyTimeDecidableLanguages Γ M ⊆ PolyTimeDecidableLanguages Γ M' := by
  intro l ⟨t, ⟨hdecide⟩⟩
  obtain ⟨t', ⟨_, time, htime⟩, hemulate⟩ := h Γ Unit t
  use t'
  use Polynomial.comp time hdecide.time
  intro a
  specialize hemulate _ _ _ (hdecide.outputsFun a)
  simpa [htime] using hemulate

/- If two computation models are equivalent in Polynomial time,
then the class `P` agrees for them.
-/
theorem P_constant (M M' : FunctionModelT) [LanguageRecognitionModel M]
    [LanguageRecognitionModel M'] (h : ComputationModel.EquivalentInPolyTime M M') (Γ : Type) :
    PolyTimeDecidableLanguages Γ M = PolyTimeDecidableLanguages Γ M' := by
  obtain ⟨_, _⟩ := h
  apply Set.eq_of_subset_of_subset
  <;> apply P_constant_aux
  <;> assumption


end AcceptingTransitionSystem
end Computation
