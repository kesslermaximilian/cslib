
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

namespace Cslib

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

/-
-- TODO: Would we like to have this instance?
instance (Γ : Type*) [DenoteAcceptance Γ] : DenoteAcceptance (Option Γ) where
  decidableEq := inferInstance
  accept := some DenoteAcceptance.accept
  reject := some DenoteAcceptance.reject
  accept_ne_reject := by simp [DenoteAcceptance.accept_ne_reject]
-/

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
View the computation model `τ` on `α` and `β` as operating on `α'` and `β'` instead,
by providing precomposition (and postcomposition) functions to (from) `α` (and `β`).
-/
structure WithIOEncoding {α β : Type*} (τ : Type*) [IOComputationModel τ α β]
    (α' β' : Type*) (enc_in : α' → α) (enc_out : Option β → Option β') where
  t : τ

instance WithIOEncoding.instIOComputationModel {α' α β β' : Type*}
    {fin : α' → α} {fout : Option β → Option β'} {τ : Type*} [IOComputationModel τ α β] :
    IOComputationModel (WithIOEncoding τ α' β' fin fout) α' β' where
  label t := label t.t
  cfg t input := cfg t.t (fin input)
  lts t input := lts t.t (fin input)
  Halted t := Halted t.t
  _Terminal_of_Halted {t} _ _ h := Terminal_of_Halted (t := t.t) h
  init t input := init t.t (fin input)
  output := fout ∘ IOComputationModel.output

/--
View the computation model `τ` as taking two list inputs (formally one input of type
`List Γ × List Γ` is needed), and model this using a computation model on `List (Option Γ)`
by encoding the two inputs using `List.combine`.
See `WithTwoInputs.instIOComputationModel` for the corresponding instance.
-/
abbrev WithTwoInputs {Γ β : Type*} (τ : Type*) [IOComputationModel τ (List (Option Γ)) β] :=
  WithIOEncoding τ (List Γ × List Γ) β (Function.uncurry List.combine) id

-- This instance can now be derived automatically
example {Γ Γ' : Type*} {τ : Type*} [IOComputationModel τ (List (Option Γ)) Γ'] :
    IOComputationModel (WithTwoInputs τ) (List Γ × List Γ) Γ' := by
  infer_instance

/--
View the computation model `τ` as an acceptor by leveraging the distinguished accept and
reject elements on its output type.
-/
abbrev AsAcceptor' {α β : Type*} (τ : Type*) [IOComputationModel τ α β] [DenoteAcceptance β] :=
  WithIOEncoding τ α Bool id (·.bind DenoteAcceptance.toBool)

-- This instance can now be derived automatically
example {α β : Type*} {τ : Type*} [IOComputationModel τ α β] [DenoteAcceptance β] :
    AcceptingCM (AsAcceptor' τ) α := by
  infer_instance

section SumType


/--
Retract of `List.map Sum.inr : List B → List (A ⊕ B)` on its image, `none` otherwise.
-/
def extractSnd {A B : Type*} (xs : List (A ⊕ B)) : Option (List B) :=
  xs.mapM fun
    | .inl _ => none
    | .inr b => some b

/-- `extractSnd` is a retract. -/
lemma inr_extractSnd_apply {A B : Type*} (xs : List B) :
    extractSnd (A := A) (List.map Sum.inr xs) = xs := by
  induction xs with
  | nil => simp [extractSnd]
  | cons xs x ih => grind [extractSnd]

/-- `extractSnd` is an isomorphism on -/
lemma Sum_inr_of_extractSnd {A B : Type*} (xs : List (A ⊕ B)) (ys : List B) :
    extractSnd xs = some ys → xs = List.map Sum.inr ys := by
  intro h
  induction xs generalizing ys with
  | nil => simpa [extractSnd] using h
  | cons x xs ih =>
    cases x
    · simp [extractSnd] at h
    · simp only [extractSnd, List.mapM_cons, Option.pure_def, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff] at h
      obtain ⟨ys', hys', heq⟩ := h
      rw [Option.some_inj] at heq
      simp [ih ys' hys', ← heq]

/--
Turn a ListTransitionSystem on a sum type into a ListTransitionSystem between the
individual types.
-/
abbrev WithSplitSum {Γ Γ' : Type*} (τ : Type*) [ListCM τ (Γ ⊕ Γ') (Γ ⊕ Γ')] :=
  WithIOEncoding (α := List (Γ ⊕ Γ')) (β := List (Γ ⊕ Γ')) τ (List Γ) (List Γ')
    (List.map Sum.inl) (fun out => out.elim none extractSnd)

-- This instance can now be derived automatically
example {Γ Γ' : Type*} (τ : Type*) [ListCM τ (Γ ⊕ Γ') (Γ ⊕ Γ')] :
    ListCM (WithSplitSum τ) Γ Γ' := by
  infer_instance

end SumType

end Cslib
