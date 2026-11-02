/-
Copyright (c) 2026 Maximilian Keßler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximilian Keßler
-/

module

public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Cslib.Computability.Machines.ComputationModel.Basic
public import Cslib.Computability.Machines.ComputationModel.Wrappers
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
open CompSize


structure ResourceUsage where
  time : ℕ
  space : ℕ
  inputSize : ℕ
  outputSize : ℕ

/-- Evaluation everywhere except space used. -/
def ResourceUsage.noSpaceValuation (R : ResourceUsage) : Fin 3 → ℕ
  | 0 => R.time
  | 1 => R.inputSize
  | 2 => R.outputSize

def ResourceUsage.mk₁ {α β : Type} [CompSize α] [CompSize β]
    (l : α) (l' : Option β) (n : ℕ) (s : ℕ) : ResourceUsage where
  time := n
  space := s
  inputSize := compSize l
  outputSize := compSize l'

namespace ComputationModel.NonDeterministic
open IOComputationModel

variable {τ τ' : Type} {τ τ' : Type*} [IOComputationModel τ α β] [IOComputationModel τ' α β]


/-- Machine `τ'` emulates (i.e. replicates computations) machine `τ`.. -/
def Emulates (t : τ) (t' : τ') :=
  ∀ ⦃l l'⦄, MayOutput t l l' → MayOutput t' l l'

/-- Machine `τ'` emulates (i.e. replicates computations) machine `τ` with overhead `time`. -/
def EmulatesInTime (t : τ) (t' : τ') (time : ℕ → ℕ) :=
  ∀ ⦃l l' n⦄, MayOutputInTime t l l' n → MayOutputInTime t' l l' (time n)

lemma EmulatesInTime.Emulates {t : τ} (t' : τ') {time : ℕ} (h : EmulatesInTime t t' time) :
    Emulates t t' := by
  rintro l l' hout
  obtain ⟨_, hout'⟩ := hout.exists_MayOutputInTime
  exact (h hout').MayOutput

lemma EmulatesInTime.Halts {t : τ} {t' : τ'} {time : ℕ → ℕ} (h : EmulatesInTime t t' time) :
    ∀ ⦃l n⦄, HaltsInTime t l n → HaltsInTime t' l (time n) := by
  intro l n h
  -- TODO: Cannot actually prove this rn

  sorry


variable (τ τ')

/--
An IOComputationModel on `τ` is reducible to `τ'` (in a specified time class),
if all transducers in `τ` have an emulator in `τ'` with time overhead given by a function
of the specified time class.
-/
def ReducibleInTime (time_class : Set (ℕ → ℕ)) :=
  ∀ (t : τ), ∃ (t' : τ') (time: time_class), EmulatesInTime t t' time

def EquivalentInTime (time_class : Set (ℕ → ℕ)) :=
  ReducibleInTime τ τ' time_class ∧ ReducibleInTime τ' τ time_class


section Space
variable [CompSize α] [CompSize β] [SpaceSize τ] [SpaceSize τ']

variable {τ τ'} in
/--
Machine `τ'` emulates (i.e. replicates computation) machine `τ` with the specified overheads:
`time_overhead` and `space_overhead` are both functions taking the four arguments
`(previous time, previous space, previous input encoding size, previous output encoding size)`
and are meant to specify the new time and space bounds.
-/
def EmulatesInTimeAndSpace (t : τ) (t' : τ') (timeBound : ResourceUsage → ℕ)
    (spaceBound : ResourceUsage → ℕ) :=
  ∀ ⦃l l' n s⦄, MayOutputInTimeAndSpace t l l' n s → MayOutputInTimeAndSpace t' l l'
      (timeBound (ResourceUsage.mk₁ l l' n s)) (spaceBound (ResourceUsage.mk₁ l l' n s))

--lemma EmulatesInTimeAndSpace.EmulatesInTime

def ReducibleInTimeAndSpace (timeBounds : Set (ResourceUsage → ℕ))
    (spaceBounds : Set (ResourceUsage → ℕ)) :=
  ∀ (t : τ), ∃ (t' : τ') (timeBound : timeBounds) (spaceBound : spaceBounds),
    EmulatesInTimeAndSpace t t' timeBound spaceBound

def EquivalentInTimeAndSpace (timeBounds : Set (ResourceUsage → ℕ))
    (spaceBounds : Set (ResourceUsage → ℕ)) :=
  ReducibleInTimeAndSpace τ τ' timeBounds spaceBounds ∧
    ReducibleInTimeAndSpace τ' τ timeBounds spaceBounds


end Space

end NonDeterministic

-- TODO: Make it easier to work with these classes

/-- Functions described by polynomials -/
def NaturalPolynomials : Set (ℕ → ℕ) := { f | ∃ (P : Polynomial ℕ), f = P.eval}

/-- Functions that are polynomially bounded by input size, output size and runtime. -/
def ResourceNoSpacePolynomials : Set (ResourceUsage → ℕ) :=
  {f | ∃ (P : MvPolynomial (Fin 3) ℕ), ∀ R, f R = P.eval R.noSpaceValuation }

/-- Functions that are polynomially bounded by space usage. -/
def ResourceSpacePolynomials : Set (ResourceUsage → ℕ) :=
  {f | ∃ (P : Polynomial ℕ), f = P.eval ∘ ResourceUsage.space}

open AcceptingCM
open IOComputationModel

/-- "Proof" that the specified tm decides the language `l` in polynomial time. -/
structure DecidesInPolyTime {Γ : Type} {τ : Type*} [ListAcceptingCM τ Γ] (t : τ)
  (l : Language Γ) where
  /-- A time function bounding execution time dependent on input size. -/
  time : Polynomial ℕ
  /-- Decision as computation of a Boolean requires agreement on accepting inputs too. -/
  accepts (w : List Γ) : w ∈ l → AcceptsInTime t w (time.eval (R := ℕ) w.length)
  rejects (w : List Γ) : w ∉ l → RejectsInTime t w (time.eval (R := ℕ) w.length)


--instance PairEncoding {Γ : Type} {τ : Type*} {β : Type}
--    [IOComputationModel τ (List (WithSeparator Γ)) β] : IOComputationModel τ (List Γ × List Γ) β
--  where
--init w := init w.first w.second
--output w := sorry
/-
structure VerificationLanguageFor {Γ : Type} (l : Language Γ) where
  certSizeBound : Polynomial ℕ
  accepting : Language (Option Γ)
  existsAccepts (w : List Γ) :
    w ∈ l → ∃ (c : List Γ), c.length ≤ certSizeBound.eval w.length ∧ List.combine w c ∈ accepting
  acceptsCorrect (w : List Γ) (c : List Γ) :
    c.length ≤ certSizeBound.eval w.length → List.combine w c ∈ accepting → w ∈ l
-/

structure Verifier {Γ : Type} (l : Language Γ) where
  -- Polynomial bound of certificate size wrt instance size
  -- (for turing machines, this is a corollary, but not generally)
  certSizeBound : Polynomial ℕ
  accept : List Γ → List Γ → Bool
  elem_iff_exists_cert (w : List Γ) :
    w ∈ l ↔ ∃ (c : List Γ), c.length ≤ certSizeBound.eval w.length ∧ accept w c

structure VerifiesInPolyTime {Γ : Type} {τ : Type*} [ListAcceptingCM τ (Option Γ)]
    (t : τ) (l : Language Γ) where
  verifier : Verifier l
  time : Polynomial ℕ
  -- Pairing instance -> certificate -> accept
  computesAccept (w c : List Γ) : c.length ≤ verifier.certSizeBound.eval w.length
    → verifier.accept w c → AcceptsInTime t (List.combine w c) (time.eval (R := ℕ) w.length)
  computesReject (w c : List Γ) : c.length ≤ verifier.certSizeBound.eval w.length →
    ¬ verifier.accept w c → RejectsInTime t (List.combine w c) (time.eval (R := ℕ) w.length)

-- More abstract version, since we don't talk about encoding
structure VerifiesInPolyTime₂ {Γ : Type} {τ : Type*} [AcceptingCM τ (List Γ × List Γ)]
    (t : τ) (l : Language Γ)
    where
  verifier : Verifier l
  --computes : IOComputationModel.ComputesInPolyTime t (Function.uncurry verifier.accept)
  time : Polynomial ℕ
  computesAccept (w c : List Γ) : c.length ≤ verifier.certSizeBound.eval w.length
    → verifier.accept w c
    → OutputsInTime t (w, c) (some true) (time.eval (R := ℕ) w.length)
  computesReject (w c : List Γ) : c.length ≤ verifier.certSizeBound.eval w.length
    → ¬ verifier.accept w c
    → OutputsInTime t (w, c) (some true) (time.eval (R := ℕ) w.length)


-- Bridging the two definitions
abbrev VerifiesInPolyTime₃ {Γ : Type} {τ : Type*} [AcceptingCM τ (List (Option Γ))]
    (t : τ) (l : Language Γ) :=
    VerifiesInPolyTime₂ (⟨t⟩ : WithTwoInputs τ) l


def DecidableInPolyTime {Γ : Type} (l : Language Γ) (τ : Type*)
    [ListAcceptingCM τ Γ]
  := ∃ (t : τ), Nonempty (DecidesInPolyTime t l)

def VerifiableInPolyTime {Γ : Type} (l : Language Γ) (τ : Type*)
    [ListAcceptingCM τ (Option Γ)]
  := ∃ (t : τ), Nonempty (VerifiesInPolyTime t l)



--def DecidableInPolyTime {Γ : Type} (l : Language Γ) (M : FunctionModelT)
    --[LanguageRecognitionModel M] :=
  --∃ (t : M Γ Unit), Nonempty (DecidesInPolyTime t l)

-- P
--def PolyTimeDecidableLanguages' (Γ : Type) (M : FunctionModelT) [LanguageRecognitionModel M] :
    --Set (Language Γ) :=
  --{ l | ∃ (t : M Γ Unit), Nonempty (DecidesInPolyTime t l) }


-- P, not bundled, not using ComputationModel
def PolyTimeDecidableLanguages (Γ : Type) (τ : Type*) [ListAcceptingCM τ Γ] :
    Set (Language Γ) :=
  { l | DecidableInPolyTime l τ }

def PolyTimeVerifiableLanguages (Γ : Type) (τ : Type*) [ListAcceptingCM τ (Option Γ)] :
    Set (Language Γ) :=
  { l | VerifiableInPolyTime l τ}


structure PolyTimeTransformable {Γ Γ' : Type} (τ : Type*) [ListCM τ Γ Γ']
    (L₁ : Language Γ) (L₂ : Language Γ') where
  f : List Γ → List Γ'
  f_correct : ∀ w, w ∈ L₁ ↔ f w ∈ L₂
  computable : IOComputationModel.PolyTimeComputable τ f


structure IsNPComplete {Γ : Type} (l : Language Γ) (τO : Type*)
    [ListAcceptingCM τO (Option Γ)]
    (τT : Type*) [ListCM τT Γ Γ] where
  elemNP : l ∈ PolyTimeVerifiableLanguages Γ τO
  transforms (l' : Language Γ): l' ∈ PolyTimeVerifiableLanguages Γ τO
    → Nonempty (PolyTimeTransformable τT l' l)


-- TODO: Can we even prove this in this generality?
-- Probably no, we have no idea how these two acceptance systems interact with
-- each other!
theorem P_sub_NP (Γ : Type) (τ τO : Type*) [ListAcceptingCM τ Γ]
    [ListAcceptingCM τO (Option Γ)] :
  PolyTimeDecidableLanguages Γ τ ⊆ PolyTimeVerifiableLanguages Γ τO := sorry


/--
"Proof" that `f` is computable in polynomial time by the system `τ`.
A witness machine and polynomial which bounds runtime are bundled as part of this structure.
structure PolyTimeComputable (f : List Γᵢ → List Γₒ) extends TimeComputable τ f where
  poly : Polynomial ℕ
  bounds : ∀ n, time_bound n ≤ poly.eval n
-/
structure TransformsInPolyTime {Γ Γ' : Type} {τ : Type*} [ListCM τ Γ Γ']
    (t : τ) (L₁ : Language Γ) (L₂ : Language Γ') where
  time : Polynomial ℕ
  f : List Γ → List Γ'
  f_correct : ∀ w, w ∈ L₁ ↔ f w ∈ L₂
  t_computes : ∀ w, IOComputationModel.OutputsInTime t w (f w) (time.eval w.length)



--def NPComplete (Γ : Type) (τ : Type*) [AcceptingTransitionSystm τ Γ] (l : Language Γ) :=


-- Sat is NP-complete
-- 1. Sat ∈ NP (Γ)                                             -> AcceptingComputationModel
-- 2. ∀ Problem ∈ NP (Γ') , ∃ PolynomialTransformation to SAT  -> ListTransitionModel Γ Γ'
--                                                             -> AcceptingComputationModel

theorem P_constant_aux {Γ : Type} (τ τ' : Type*) [ListAcceptingCM τ Γ]
    [ListAcceptingCM τ' Γ]
    (h : IOComputationModel.ReducibleInTime τ τ' NaturalPolynomials) :
    PolyTimeDecidableLanguages Γ τ ⊆ PolyTimeDecidableLanguages Γ τ' := by
  intro l ⟨t, ⟨hdecide⟩⟩
  obtain ⟨t', ⟨_, time, htime⟩, hemulate⟩ := h t
  use t'
  use Polynomial.comp time hdecide.time
  <;> intro w hw
  · unfold AcceptsInTime
    unfold HaltsInTime ComputationModel.HaltsFromInTime
    obtain ⟨hhalts, hout⟩ := (hdecide.accepts w hw)

    --specialize hemulate _ _ _ hout

    constructor
    · sorry
    · sorry
  · sorry
  --· --have := hdecide.accepts w hw
    --specialize hemulate _ _ _ (hdecide.accepts w hw)
    --simpa [htime] using hemulate
  --· specialize hemulate _ _ _ (hdecide.rejects w hw)
    --simpa [htime] using hemulate

/- If two computation models are equivalent in Polynomial time,
then the class `P` agrees for them.
-/
theorem P_constant {Γ : Type} (τ τ' : Type*) [ListAcceptingCM τ Γ]
    [ListAcceptingCM τ' Γ]
    (h : IOComputationModel.EquivalentInTime τ τ' NaturalPolynomials) :
    PolyTimeDecidableLanguages Γ τ = PolyTimeDecidableLanguages Γ τ' := by
  obtain ⟨_, _⟩ := h
  apply Set.eq_of_subset_of_subset
  <;> apply P_constant_aux
  <;> assumption

end Computation
