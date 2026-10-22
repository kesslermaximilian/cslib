/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Cslib.Computability.Machines.ComputationModel.Basic
public import Cslib.Foundations.Relation.RelatesInSteps
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Computability.Language
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Logic.Function.Iterate
public import Cslib.Foundations.Data.List.Combine

/-! test-/

@[expose] public section


namespace Computation


structure ResourceUsage where
  time : ℕ
  space : ℕ
  inputEncodingSize : ℕ
  outputEncodingSize : ℕ

/-- Evaluation everywhere except space used. -/
def ResourceUsage.noSpaceValuation (R : ResourceUsage) : Fin 3 → ℕ
  | 0 => R.time
  | 1 => R.inputEncodingSize
  | 2 => R.outputEncodingSize

namespace IOTransitionSystem
open Cslib.Automata
open IOTransitionSystem

/--
Machine `τ'` emulates (i.e. replicates computations) machine `τ` with overhead `time`. -/
def EmulatesInTime (Γ Γ' : Type) {α β : Type*} [IOTransitionSystem α Γ Γ']
  [IOTransitionSystem β Γ Γ'] (τ : α) (τ' : β) (time : ℕ → ℕ) :=
  ∀ (l : Γ), ∀ (l' : Option Γ') n,
    OutputsInTime τ l l' n → OutputsInTime τ' l l' (time n)


def ResourceUsage.mk₁ {Γ Γ' : Type} [EncodingSize Γ] [EncodingSize Γ']
    (l : Γ) (l' : Option Γ') (n : ℕ) (s : ℕ) : ResourceUsage where
  time := n
  space := s
  inputEncodingSize := EncodingSize.encodingSize l
  outputEncodingSize := EncodingSize.encodingSize l'


-- TODO: Generalize this for other resources apart from time/space ?

/--
Machine `τ'` emulates (i.e. replicates computation) machine `τ` with the specified overheads:
`time_overhead` and `space_overhead` are both functions taking the four arguments
`(previous time, previous space, previous input encoding size, previous output encoding size)`
and are meant to specify the new time and space bounds.
-/
def EmulatesInTimeAndSpace (Γ Γ' : Type) [EncodingSize Γ] [EncodingSize Γ'] {α β : Type*}
    [IOTransitionSystem α Γ Γ'] [SpaceSize α] [IOTransitionSystem β Γ Γ'] [SpaceSize β]
    (τ : α) (τ' : β) (timeBound : ResourceUsage → ℕ) (spaceBound : ResourceUsage → ℕ):=
  ∀ (l : Γ), ∀ (l' : Option Γ') n s,
    OutputsInTimeAndSpace τ l l' n s
    → OutputsInTimeAndSpace τ' l l'
      (timeBound (ResourceUsage.mk₁ l l' n s)) (spaceBound (ResourceUsage.mk₁ l l' n s))

/--
An IOTransitionSystem on `α` is reducible to `β` (in a specified time class),
if all transducers in `α` have an emulator in `β` with time overhead given by a function
of the specified time class.
-/
def ReducibleInTime {Γ Γ' : Type} (α β : Type*) [IOTransitionSystem α Γ Γ']
    [IOTransitionSystem β Γ Γ'] (time_class : Set (ℕ → ℕ)) :=
  ∀ (τ : α), ∃ (τ' : β) (time: time_class), EmulatesInTime Γ Γ' τ τ' time

def EquivalentInTime {Γ Γ' : Type} (α β : Type*) [IOTransitionSystem α Γ Γ']
    [IOTransitionSystem β Γ Γ'] (time_class : Set (ℕ → ℕ)) :=
  ReducibleInTime α β time_class ∧ ReducibleInTime β α time_class

def ReducibleInTimeAndSpace {Γ Γ' : Type} [EncodingSize Γ] [EncodingSize Γ'] (α β : Type u)
    [IOTransitionSystem α Γ Γ'] [SpaceSize α] [IOTransitionSystem β Γ Γ']
    [SpaceSize β] (timeBounds : Set (ResourceUsage → ℕ))
    (spaceBounds : Set (ResourceUsage → ℕ)) :=
  ∀ (τ : α), ∃ (τ' : β) (timeBound : timeBounds) (spaceBound : spaceBounds),
    EmulatesInTimeAndSpace Γ Γ' τ τ' timeBound spaceBound

def EquivalentInTimeAndSpace {Γ Γ' : Type} [EncodingSize Γ] [EncodingSize Γ'] (α β : Type u)
    [IOTransitionSystem α Γ Γ'] [SpaceSize α] [IOTransitionSystem β Γ Γ']
    [SpaceSize β] (timeBounds : Set (ResourceUsage → ℕ))
    (spaceBounds : Set (ResourceUsage → ℕ)) :=
  ReducibleInTimeAndSpace α β timeBounds spaceBounds ∧
    ReducibleInTimeAndSpace β α timeBounds spaceBounds


end IOTransitionSystem


-- TODO: Make it easier to work with these classes

/-- Functions described by polynomials -/
def NaturalPolynomials : Set (ℕ → ℕ) := { f | ∃ (P : Polynomial ℕ), f = P.eval}

/-- Functions that are polynomially bounded by input size, output size and runtime. -/
def ResourceNoSpacePolynomials : Set (ResourceUsage → ℕ) :=
  {f | ∃ (P : MvPolynomial (Fin 3) ℕ), ∀ R, f R = P.eval R.noSpaceValuation }

/-- Functions that are polynomially bounded by space usage. -/
def ResourceSpacePolynomials : Set (ResourceUsage → ℕ) :=
  {f | ∃ (P : Polynomial ℕ), f = P.eval ∘ ResourceUsage.space}

open AcceptingTransitionSystem

/-- "Proof" that the specified tm decides the language `l` in polynomial time. -/
structure DecidesInPolyTime {Γ : Type} {τ : Type*} [AcceptingTransitionSystem τ Γ] (t : τ)
  (l : Language Γ) where
  /-- A time function bounding execution time dependent on input size. -/
  time : Polynomial ℕ
  accepts (w : List Γ) : w ∈ l → AcceptsInTime t w (time.eval (R := ℕ) w.length)
  rejects (w : List Γ) : w ∉ l → RejectsInTime t w (time.eval (R := ℕ) w.length)

structure Verifier {Γ : Type} (l : Language Γ) where
  accepts : List Γ → List Γ → Bool
  existsAccepts (w : List Γ) : w ∈ l → ∃ c, accepts w c = True
  acceptsCorrect (w c: List Γ) : accepts w c = True → w ∈ l

-- More abstract version, since we don't talk about encoding
structure VerifiesInPolyTime₂ {Γ : Type} {τ : Type*} [IOTransitionSystem τ (List Γ × List Γ) Bool]
    (t : τ) (l : Language Γ)
    where
  verifier : Verifier l
  -- Note: Depends on encoding Size defined on of `List Γ × List Γ`
  computes : IOTransitionSystem.ComputesInPolyTime t (Function.uncurry verifier.accepts)

/-- Equivalent to `Option α`, but different naming -/
inductive WithSeparator (α : Type u) where
  /-- No value. -/
  | separator : WithSeparator α
  /-- Some value of type `α`. -/
  | some (val : α) : WithSeparator α

--instance PairEncoding {Γ : Type} {τ : Type*} {β : Type}
--    [IOTransitionSystem τ (List (WithSeparator Γ)) β] : IOTransitionSystem τ (List Γ × List Γ) β
--  where
--init w := init w.first w.second
--output w := sorry

structure VerificationLanguageFor {Γ : Type} (l : Language Γ) where
  accepting : Language (Option Γ)
  existsAccepts (w : List Γ) : w ∈ l → ∃ (c : List Γ), List.combine w c ∈ accepting
  acceptsCorrect (w : List Γ) (c : List Γ) : List.combine w c ∈ accepting → w ∈ l


structure VerifiesInPolyTime {Γ : Type} {τ : Type*} [AcceptingTransitionSystem τ (Option Γ)]
    (t : τ) (l : Language Γ) where
  language : VerificationLanguageFor l
  verifies : DecidesInPolyTime t language.accepting


def DecidableInPolyTime {Γ : Type} (l : Language Γ) (τ : Type*) [AcceptingTransitionSystem τ Γ]
  := ∃ (t : τ), Nonempty (DecidesInPolyTime t l)

def VerifiableInPolyTime {Γ : Type} (l : Language Γ) (τ : Type*)
    [AcceptingTransitionSystem τ (Option Γ)]
  := ∃ (t : τ), Nonempty (VerifiesInPolyTime t l)



--def DecidableInPolyTime {Γ : Type} (l : Language Γ) (M : FunctionModelT)
    --[LanguageRecognitionModel M] :=
  --∃ (t : M Γ Unit), Nonempty (DecidesInPolyTime t l)

-- P
--def PolyTimeDecidableLanguages' (Γ : Type) (M : FunctionModelT) [LanguageRecognitionModel M] :
    --Set (Language Γ) :=
  --{ l | ∃ (t : M Γ Unit), Nonempty (DecidesInPolyTime t l) }


-- P, not bundled, not using ComputationModel
def PolyTimeDecidableLanguages (Γ : Type) (τ : Type*) [AcceptingTransitionSystem τ Γ] :
    Set (Language Γ) :=
  { l | DecidableInPolyTime l τ }

def PolyTimeVerifiableLanguages (Γ : Type) (τ : Type*) [AcceptingTransitionSystem τ (Option Γ)] :
    Set (Language Γ) :=
  { l | VerifiableInPolyTime l τ}


structure PolyTimeTransformable {Γ Γ' : Type} (τ : Type*) [ListTransitionSystem τ Γ Γ']
    (L₁ : Language Γ) (L₂ : Language Γ') where
  f : List Γ → List Γ'
  f_correct : ∀ w, w ∈ L₁ ↔ f w ∈ L₂
  computable : IOTransitionSystem.PolyTimeComputable τ f


structure IsNPComplete {Γ : Type} (l : Language Γ) (τO : Type*)
    [AcceptingTransitionSystem τO (Option Γ)]
    (τT : Type*) [ListTransitionSystem τT Γ Γ] where
  elemNP : l ∈ PolyTimeVerifiableLanguages Γ τO
  transforms (l' : Language Γ): l' ∈ PolyTimeVerifiableLanguages Γ τO
    → Nonempty (PolyTimeTransformable τT l l')


-- TODO: Can we even prove this in this generality?
-- Probably no, we have no idea how these two acceptance systems interact with
-- each other!
theorem P_sub_NP (Γ : Type) (τ τO : Type*) [AcceptingTransitionSystem τ Γ]
    [AcceptingTransitionSystem τO (Option Γ)] :
  PolyTimeDecidableLanguages Γ τ ⊆ PolyTimeVerifiableLanguages Γ τO := sorry


/--
"Proof" that `f` is computable in polynomial time by the system `τ`.
A witness machine and polynomial which bounds runtime are bundled as part of this structure.
structure PolyTimeComputable (f : List Γᵢ → List Γₒ) extends TimeComputable τ f where
  poly : Polynomial ℕ
  bounds : ∀ n, time_bound n ≤ poly.eval n
-/
structure TransformsInPolyTime {Γ Γ' : Type} {τ : Type*} [ListTransitionSystem τ Γ Γ']
    (t : τ) (L₁ : Language Γ) (L₂ : Language Γ') where
  time : Polynomial ℕ
  f : List Γ → List Γ'
  f_correct : ∀ w, w ∈ L₁ ↔ f w ∈ L₂
  t_computes : ∀ w, IOTransitionSystem.OutputsInTime t w (f w) (time.eval w.length)



--def NPComplete (Γ : Type) (τ : Type*) [AcceptingTransitionSystm τ Γ] (l : Language Γ) :=


-- Sat is NP-complete
-- 1. Sat ∈ NP (Γ)                                             -> AcceptingTransitionSystem
-- 2. ∀ Problem ∈ NP (Γ') , ∃ PolynomialTransformation to SAT  -> ListTransitionModel Γ Γ'
--                                                             -> AcceptingTransitionSystem

theorem P_constant_aux {Γ : Type} (τ τ' : Type*) [AcceptingTransitionSystem τ Γ]
    [AcceptingTransitionSystem τ' Γ]
    (h : IOTransitionSystem.ReducibleInTime τ τ' NaturalPolynomials) :
    PolyTimeDecidableLanguages Γ τ ⊆ PolyTimeDecidableLanguages Γ τ' := by
  intro l ⟨t, ⟨hdecide⟩⟩
  obtain ⟨t', ⟨_, time, htime⟩, hemulate⟩ := h t
  use t'
  use Polynomial.comp time hdecide.time
  <;> intro w hw
  · specialize hemulate _ _ _ (hdecide.accepts w hw)
    simpa [htime] using hemulate
  · specialize hemulate _ _ _ (hdecide.rejects w hw)
    simpa [htime] using hemulate

/- If two computation models are equivalent in Polynomial time,
then the class `P` agrees for them.
-/
theorem P_constant {Γ : Type} (τ τ' : Type*) [AcceptingTransitionSystem τ Γ]
    [AcceptingTransitionSystem τ' Γ]
    (h : IOTransitionSystem.EquivalentInTime τ τ' NaturalPolynomials) :
    PolyTimeDecidableLanguages Γ τ = PolyTimeDecidableLanguages Γ τ' := by
  obtain ⟨_, _⟩ := h
  apply Set.eq_of_subset_of_subset
  <;> apply P_constant_aux
  <;> assumption

end Computation
