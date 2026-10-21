
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
public import Cslib.Computability.Machines.ComputationModel.Basic
public import Mathlib.Computability.Language
public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Cslib.Computability.Machines.ComputationModel.Equivalence

/-! test-/

@[expose] public section


namespace Computation
-- TODO: Should we fix the type universe here, or be more flexible?
--universe u v
-- TODO: Fintype?
abbrev FunctionModelT := Type -> Type -> Type*

class ComputationModel (M : FunctionModelT) (InType : outParam (Type -> Type))
    (OutType : outParam (Type -> Type)) where
  transitionSystem: ∀ Γ Γ', IOTransitionSystem.{u, v} (M Γ Γ') (InType Γ) (OutType Γ')

class SpaceComputationModel (M : FunctionModelT) (InType : outParam (Type -> Type))
    (OutType : outParam (Type -> Type)) extends ComputationModel M InType OutType where
  space : ∀ Γ Γ', SpaceSize (M Γ Γ')

abbrev FunctionComputationModel (M : FunctionModelT) :=
  ComputationModel M List List

abbrev SpaceFunctionComputationModel (M : FunctionModelT) :=
  SpaceComputationModel M List List

abbrev LanguageRecognitionModel (M : FunctionModelT) :=
  ComputationModel M List (fun _ => Bool)

abbrev SpaceLanguageRecognitionModel (M : FunctionModelT) :=
  SpaceComputationModel M List (fun _ => Bool)

namespace ComputationModel


-- General instance exposing the typeclass synthesis
instance (M : FunctionModelT) (InType OutType : Type -> Type) [ComputationModel M InType OutType]
    (Γ Γ' : Type): IOTransitionSystem (M Γ Γ') (InType Γ) (OutType Γ') :=
  ComputationModel.transitionSystem Γ Γ'

-- General instance exposing the typeclass synthesis
instance (M : FunctionModelT) (InType OutType : Type -> Type)
    [SpaceComputationModel M InType OutType] (Γ Γ' : Type): SpaceSize (M Γ Γ') :=
  SpaceComputationModel.space Γ Γ'

-- Duplicate, not needed, but here for checking
instance (M : FunctionModelT) [FunctionComputationModel M] (Γ Γ' : Type) :
    ListTransitionSystem (M Γ Γ') Γ Γ' := by
  infer_instance

-- Duplicate, not needed, but here for checking
instance (M : FunctionModelT) [LanguageRecognitionModel M] (Γ : Type) :
    AcceptingTransitionSystem (M Γ Bool) Γ := by
  infer_instance

def ReducibleInTime (M M' : FunctionModelT) {InType OutType}
    [ComputationModel M InType OutType] [ComputationModel M' InType OutType]
    (timeBounds : Set (ℕ → ℕ)) :=
  ∀ Γ Γ', IOTransitionSystem.ReducibleInTime (M Γ Γ') (M' Γ Γ') timeBounds

def ReducibleInTimeAndSpace (M M' : FunctionModelT) {InType OutType : Type → Type}
    [SpaceComputationModel M InType OutType] [SpaceComputationModel M' InType OutType]
    (timeBounds : Set (ResourceUsage → ℕ)) (spaceBounds : Set (ResourceUsage → ℕ)) :=
  ∀ (Γ Γ' : Type) [EncodingSize (InType Γ)] [EncodingSize (OutType Γ')],
    IOTransitionSystem.ReducibleInTimeAndSpace (M Γ Γ') (M' Γ Γ') timeBounds spaceBounds

def EquivalentInTime (M M' : FunctionModelT) {InType OutType}
    [ComputationModel M InType OutType] [ComputationModel M' InType OutType]
    (time_class : Set (ℕ → ℕ)) :=
  ReducibleInTime M M' time_class ∧ ReducibleInTime M' M time_class

def EquivalentInTimeAndSpace (M M' : FunctionModelT) {InType OutType : Type → Type}
    [SpaceComputationModel M InType OutType] [SpaceComputationModel M' InType OutType]
    (timeBounds : Set (ResourceUsage → ℕ)) (spaceBounds : Set (ResourceUsage → ℕ)) :=
  ReducibleInTimeAndSpace M M' timeBounds spaceBounds ∧
    ReducibleInTimeAndSpace M' M timeBounds spaceBounds


abbrev ReducibleInPolyTime (M : FunctionModelT) (M' : FunctionModelT) {InType OutType}
    [ComputationModel M InType OutType] [ComputationModel M' InType OutType] :=
    ReducibleInTime M M' NaturalPolynomials

abbrev EquivalentInPolyTime (M M' : FunctionModelT) {InType OutType}
    [ComputationModel M InType OutType] [ComputationModel M' InType OutType] :=
  EquivalentInTime M M' NaturalPolynomials

abbrev ReducibleInPolyTimeAndPolySpace (M M' : FunctionModelT) {InType OutType : Type → Type}
    [SpaceComputationModel M InType OutType] [SpaceComputationModel M' InType OutType] :=
  ReducibleInTimeAndSpace M M' ResourceNoSpacePolynomials ResourceSpacePolynomials

abbrev EquivalentInPolyTimeAndPolySpace (M M' : FunctionModelT) {InType OutType : Type → Type}
    [SpaceComputationModel M InType OutType] [SpaceComputationModel M' InType OutType] :=
  EquivalentInTimeAndSpace M M' ResourceNoSpacePolynomials ResourceSpacePolynomials

-- BAD
--structure BundledLanguage where
--  Γ : Type
--  L : Language Γ

-- P, Bundled
--def PolyTimeDecidableBundledLanguages (M : FunctionModelT) [LanguageRecognitionModel M] :
    --Set (BundledLanguage) :=
  --{ l | ∃ (t : M l.Γ Unit), Nonempty (DecidesInPolyTime t l.L) }
end ComputationModel

end Computation
