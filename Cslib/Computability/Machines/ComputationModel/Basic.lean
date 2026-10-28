/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Cslib.Foundations.Relation.RelatesInSteps
public import Cslib.Foundations.Semantics.LTS.Relation
public import Cslib.Foundations.Semantics.LTS.Execution
public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Cslib.Computability.Machines.ComputationModel.EncodingSize


/-! # Computation models based on labelled transition systems

Each computer `t` has a configuration type `cfg t`, a label type `label t`, and
an `LTS (cfg t) (label t)`. `IOTransitionSystem` adds an initial configuration
for each input and a partial output function.

Execution uses the existing LTS API: `EvalsTo` is `LTS.CanReach`, and
`EvalsToInTime` witnesses an `LTS.MTr` whose list of labels has length at most
the time bound. Every transition counts as one step, regardless of its label.
Halting means that the final configuration satisfies `LTS.IsTerminal`.
These predicates express the existence of an execution; they do not require
that every execution terminate or that the LTS be deterministic.

## Main declarations

- `TransitionSystem`: configuration types, label types, and an LTS for each computer.
- `IOTransitionSystem`: a transition system with input initialization and partial output.
- `TransitionSystem.EvalsTo`, `TransitionSystem.EvalsToInTime`: reachability and
  time-bounded reachability in the associated LTS.
- `IOTransitionSystem.HaltingRun`, `IOTransitionSystem.HaltingRunInTime`: reachable
  terminal configurations, optionally with a bound on the number of transitions.
- `IOTransitionSystem.OutputsInTime`: output of a halting execution within a time bound.
- `IOTransitionSystem.TimeComputable`, `IOTransitionSystem.PolyTimeComputable`:
  computers bundled with bounds on the time needed to compute a function.

The time-and-space records currently bound only the final configuration's
space usage. A bound on space throughout an execution requires the intermediate
states recorded by `LTS.Execution` and is left for a separate development.
-/

@[expose] public section

namespace Computation

open Cslib

open EncodingSize

/-- A configuration type, label type, and labelled transition system for each computer. -/
class ComputationModel (τ : Type u) where
  /-- Configuration type (or state type) associated with a computer -/
  cfg (t : τ) : Type v
  /-- Label type associated with the LTS of a computer -/
  label (t : τ) : Type w
  /-- Resulting LTS of a computer -/
  lts (t : τ) : LTS (cfg t) (label t)

class SpaceSize (τ : Type u) [ComputationModel τ] where
  space_used {t : τ} : ComputationModel.cfg t → ℕ

/--
Bundles a `TransitionSystem` with input and output functions from/to types `α` and `β`.
This way, we can think of elements of `τ` as allowing computations `α → β` by lifting inputs into
the computation context, following labelled transitions and taking output from this computation
context.
-/
class IOComputationModel (τ : Type u) (α β : outParam Type) extends ComputationModel τ
    where
  init {t : τ} : α → cfg t
  output {t : τ} : cfg t → Option β

-- Configuration and label universes are independent and occur together in these aliases.
set_option linter.checkUnivs false in
/-- An `IOTransitionSystem` between `List Γᵢ` and `List Γₒ`. -/
abbrev ListCM (τ : Type*) (Γᵢ Γₒ : Type) := IOComputationModel τ (List Γᵢ) (List Γₒ)

set_option linter.checkUnivs false in
/-- An `IOTransitionSystem` between `α` and `Bool`.
`True` and `False` denote acceptance and rejection. -/
abbrev AcceptingCM (τ : Type*) (α : Type) := IOComputationModel τ α Bool

set_option linter.checkUnivs false in
/-- An `IOTransitionSystem` between `List Γ` and `Bool`.
`True` and `False` denote acceptance and rejection. -/
abbrev ListAcceptingCM (τ : Type*) (Γ : Type) := IOComputationModel τ (List Γ) Bool

open ComputationModel

namespace TransitionSystem

variable {τ : Type u} [ComputationModel τ]

/-- Reachability in the computer's labelled transition system. -/
def EvalsTo (t : τ) (a b : cfg t) := LTS.CanReach (lts t) a b

/--
The machine `t` reaches `b` from `a` in at most `n` steps.
-/
def EvalsToInTime (t : τ) (a b : cfg t) (n : ℕ) :=
  LTS.CanReachIn (lts t) a b n

variable {t : τ} {a b c : cfg t} {n n₁ n₂ : ℕ}

lemma EvalsTo.refl : EvalsTo t a a := LTS.CanReach.refl (lts t) a

lemma EvalsTo.trans (h₁ : EvalsTo t a b) (h₂ : EvalsTo t b c) : EvalsTo t a c
  := LTS.CanReach.trans h₁ h₂

lemma EvalsToInTime.refl : EvalsToInTime t a a 0 := LTS.CanReachIn.refl _ _

lemma EvalsToInTime.trans (h₁ : EvalsToInTime t a b n₁) (h₂ : EvalsToInTime t b c n₂) :
    EvalsToInTime t a c (n₁ + n₂) := LTS.CanReachIn.trans h₁ h₂

lemma EvalsToInTime.mono : Monotone (EvalsToInTime t a b ·) := LTS.CanReachIn.mono _

/-- A bounded execution also witnesses unbounded reachability. -/
theorem EvalsToInTime.evalsTo (h : EvalsToInTime t a b n) : EvalsTo t a b := h.toCanReach

/- Recover the counted-relation API by forgetting transition labels. -/
--theorem evalsToInTime_iff_relatesWithinSteps :
    --EvalsToInTime t a b n ↔ Relation.RelatesWithinSteps (lts t).UnlabelledTr a b n :=
  --(lts t).relatesWithinSteps_unlabelledTr_iff.symm

end TransitionSystem

namespace IOComputationModel
open ComputationModel

variable {τ : Type*} {α β : Type} [IOComputationModel τ α β]

/--
A valid execution sequence that halts.
-/
structure HaltingRun (t : τ) (l : α) where
  μs : List (label t)
  ss : List (cfg t)
  haltState : (cfg t)
  haltState_halts : (lts t).IsTerminal haltState
  isExecution : LTS.Execution (lts t) (init l) μs haltState ss

/--
A valid execution sequence that halts within time bound `n`.
-/
structure HaltingRunInTime (t : τ) (l : α) (n : ℕ) extends HaltingRun t l where
  lengthBound : μs.length ≤ n

structure HaltingRunInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (n : ℕ) (s : ℕ)
    extends HaltingRunInTime t l n where
  size_bound : ∀ state ∈ ss, SpaceSize.space_used state ≤ s

def Halts (t : τ) (l : α) :=
  Nonempty (HaltingRun t l)

/--
Time bounds of `HaltingRunInTime` can be increased.
-/
def HaltingRunInTime.mono {t : τ} {n m : ℕ} {l : α} (hnm : n ≤ m)
    (hv : HaltingRunInTime t l n) : HaltingRunInTime t l m where
  μs := hv.μs
  ss := hv.ss
  haltState := hv.haltState
  haltState_halts := hv.haltState_halts
  isExecution := hv.isExecution
  lengthBound := Nat.le_trans hv.lengthBound hnm

def HaltsInTime (t : τ) (l : α) (n : ℕ) :=
  Nonempty (HaltingRunInTime t l n)

theorem HaltsInTime.mono {t : τ} {l : α} : Monotone (HaltsInTime t l ·) := by
  intro _ _ hnm ⟨h⟩
  exact ⟨h.mono hnm⟩

def Outputs (t : τ) (l : α) (l' : Option β) :=
  ∃ (run : HaltingRun t l), output run.haltState = l'

def OutputsInTime (t : τ) (l : α) (l' : Option β) (n : ℕ) :=
  ∃ (run : HaltingRunInTime t l n), output run.haltState = l'

def OutputsInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (l' : Option β) (n : ℕ) (s : ℕ) :=
  ∃ (run : HaltingRunInTimeAndSpace t l n s), output run.haltState = l'

theorem OutputsInTime.mono {t : τ} {l : α} {l' : Option β} : Monotone (OutputsInTime t l l' · )
    := by
  intro _ _ hnm ⟨h, heq⟩
  exact ⟨h.mono hnm, heq⟩

def ComputesInTime [EncodingSize α] (t : τ) (f : α → β) (time : ℕ → ℕ) :=
  ∀ (l : α), OutputsInTime t l (some (f l)) (time (EncodingSize.encodingSize l))

def ComputesInPolyTime [EncodingSize α] (t : τ) (f : α → β) :=
  ∃ (P : Polynomial ℕ), ComputesInTime t f P.eval

/--
"Proof" that `f` is computable by the system `τ`.
A witness machine is bundled as part of this structure,
as well as a function bounding execution time.
-/
structure TimeComputable {Γ Γ' : Type} [EncodingSize Γ]
    (τ : Type*) [IOComputationModel τ Γ Γ'] (f : Γ → Γ') where
  t : τ
  timeBound : ℕ → ℕ
  outputsFunInTmie : ∀ w, OutputsInTime t w (f w) (timeBound (encodingSize w))

structure PolyTimeComputable {Γ Γ' : Type} [EncodingSize Γ]
    (τ : Type*) [IOComputationModel τ Γ Γ'] (f : Γ → Γ') extends TimeComputable τ f where
  poly : Polynomial ℕ
  bounds (n : ℕ) : timeBound n ≤ poly.eval n

end IOComputationModel


namespace AcceptingCM
open IOComputationModel

variable {τ : Type*} {α : Type} [AcceptingCM τ α]

abbrev AcceptsInTime (t : τ) (l : α) (n : ℕ) :=
  OutputsInTime t l (Option.some true) n

abbrev AcceptsInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (n : ℕ) (s : ℕ) :=
  OutputsInTimeAndSpace t l (Option.some true) n s

abbrev RejectsInTime (t : τ) (l : α) (n : ℕ) :=
  OutputsInTime t l (Option.some false) n

abbrev RejectsInTimeAndSpace [SpaceSize τ] (t : τ) (l : α) (n : ℕ) (s : ℕ) :=
  OutputsInTimeAndSpace t l Option.none n s

theorem AcceptsInTime.mono {t : τ} {l : α} : Monotone (AcceptsInTime t l · ) :=
  OutputsInTime.mono

theorem RejectsInTime.mono {t : τ} {l : α} : Monotone (AcceptsInTime t l · ) :=
  OutputsInTime.mono

theorem DecidesInTime.mono {t : τ} {l : α} : Monotone (AcceptsInTime t l · ) :=
  OutputsInTime.mono

end AcceptingCM


end Computation
