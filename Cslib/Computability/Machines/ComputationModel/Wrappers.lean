
/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Cslib.Computability.Machines.ComputationModel.Basic
public import Cslib.Foundations.Data.List.Combine


/-!
# TODO
-/

@[expose] public section

namespace Computation

open ComputationModel
open IOComputationModel

/-- Marks distinguished `accept` and `reject` elements in a type, required to be different. -/
class DenoteAcceptance (Γ : Type*) where
  decidableEq : DecidableEq Γ
  accept : Γ
  reject : Γ
  accept_ne_reject : accept ≠ reject

instance {Γ : Type*} [h : DenoteAcceptance Γ] : DecidableEq Γ :=
  h.decidableEq


instance (Γ : Type*) [DenoteAcceptance Γ] : DenoteAcceptance (Option Γ) where
  decidableEq := inferInstance
  accept := some DenoteAcceptance.accept
  reject := some DenoteAcceptance.reject
  accept_ne_reject := by simp [DenoteAcceptance.accept_ne_reject]

instance (Γ : Type*) [DenoteAcceptance Γ] : DenoteAcceptance (List Γ) where
  decidableEq := inferInstance
  accept := [DenoteAcceptance.accept]
  reject := [DenoteAcceptance.reject]
  accept_ne_reject := by simp [DenoteAcceptance.accept_ne_reject]

def DenoteAcceptance.toBool {Γ : Type*} [DenoteAcceptance Γ] (t : Γ) : Option Bool :=
  if t = DenoteAcceptance.accept then some true
  else if t = DenoteAcceptance.reject then some false
  else none

/--
View the computation model `τ` as taking two list inputs (formally one input of type
`List Γ × List Γ` is needed), and model this using a computation model on `List (Option Γ)`
by encoding the two inputs using `List.combine`.
See `WithTwoInputs.instIOComputationModel` for the corresponding instance.
-/
structure WithTwoInputs (τ : Type*) where
  t : τ

instance WithTwoInputs.instIOComputationModel {Γ Γ' : Type} {τ : Type*}
    [IOComputationModel τ (List (Option Γ)) Γ'] :
    IOComputationModel (WithTwoInputs τ) (List Γ × List Γ) Γ'  where
  label w := ComputationModel.label w.t
  lts w := ComputationModel.lts w.t
  cfg a := ComputationModel.cfg a.t
  init input := IOComputationModel.init (List.combine input.fst input.snd)
  output := IOComputationModel.output

/--
View the computation model `τ` as an acceptor by leveraging the distinguished accept and
reject elements on its output type.
-/
structure AsAcceptor (τ : Type*) where
  t : τ

instance {Γ Γ' : Type} {τ : Type*} [IOComputationModel τ Γ Γ'] [DenoteAcceptance Γ'] :
    IOComputationModel (AsAcceptor τ) Γ Bool  where
  cfg a := cfg a.t
  label a := label a.t
  lts a := lts a.t
  init := init
  output w := output w >>= DenoteAcceptance.toBool


section SumType

/--
Turn a ListTransitionSystem on a sum type into a ListTransitionSystem between the
individual types.
-/
structure WithSplitSum (τ : Type*) where
  t : τ

/--
Retract of `List.map Sum.inr : List B → List (A ⊕ B)` on its image, `none` otherwise.
-/
def extractSnd {A B : Type} (xs : List (A ⊕ B)) : Option (List B) :=
  xs.mapM fun
    | .inl _ => none
    | .inr b => some b

lemma inr_extractSnd_apply {A B : Type} (xs : List B) :
    extractSnd (A := A) (List.map Sum.inr xs) = xs := by
  induction xs with
  | nil => simp [extractSnd]
  | cons xs x ih => grind [extractSnd]

instance {Γ Γ' : Type} (τ : Type*) [ListCM τ (Γ ⊕ Γ') (Γ ⊕ Γ')] :
    ListCM (WithSplitSum τ) Γ Γ' where
  cfg a := cfg a.t
  label a := label a.t
  lts a := lts a.t
  init := init ∘ (List.map Sum.inl)
  output w := output w >>= extractSnd

end SumType

end Computation
