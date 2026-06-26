/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import Cslib.Foundations.Data.StackTape
public import Mathlib.Computability.TuringMachine.Tape
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Tactic.NormNum

/-!
# BiTape: Bidirectionally infinite TM tape representation using StackTape

This file defines `BiTape`, a tape representation for Turing machines
in the form of an `List` of `Option` values,
with the additional property that the list cannot end with `none`.

## Design

Note that Mathlib has a `Tape` type, but it requires the alphabet type to be inhabited,
and considers the ends of the tape to be filled with default values.

This design requires the tape elements to be `Option` values, and ensures that
`List`s of the base alphabet, rendered directly onto the tape by mapping over `some`,
will not collide.

## Main definitions

* `BiTape`: A tape with a head symbol and left/right contents stored as `StackTape`
* `BiTape.move`: Move the tape head left or right
* `BiTape.write`: Write a symbol at the current head position
* `BiTape.spaceUsed`: The space used by the tape
-/

@[expose] public section

namespace Turing

/--
A structure for bidirectionally-infinite Turing machine tapes
that eventually take on blank `none` values
-/
structure BiTape (Symbol : Type) where
  /-- The symbol currently under the tape head -/
  head : Option Symbol
  /-- The contents to the left of the head -/
  left : StackTape Symbol
  /-- The contents to the right of the head -/
  right : StackTape Symbol

namespace BiTape

variable {Symbol : Type}

/-- The empty `BiTape` -/
def nil : BiTape Symbol := ⟨none, ∅, ∅⟩

instance : Inhabited (BiTape Symbol) where
  default := nil

instance : EmptyCollection (BiTape Symbol) :=
  ⟨nil⟩

@[simp]
lemma empty_eq_nil : (∅ : BiTape Symbol) = nil := rfl

/--
Given a `List` of `Symbol`s, construct a `BiTape` by mapping the list to `some` elements
and laying them out to the right side,
with the head under the first element of the list if it exists.
-/
def mk₁ (l : List Symbol) : BiTape Symbol :=
  match l with
  | [] => ∅
  | h :: t => { head := some h, left := ∅, right := StackTape.mapSome t }

section Retract

/-! # Retract of `mk₁`
We want to define a retract of the function `mk₁`.
-/

/-- Extracts a list of `Symbol` from the right hand side of the tape (including head) by
dropping `none` entries.
This is a retract to `BiTape.mk₁`, see `mk₁_extract`
-/
def extract (t : BiTape Symbol) : List Symbol := List.reduceOption (t.head :: t.right.toList)

theorem mk₁_extract (l : List Symbol) : (mk₁ l).extract = l := by
  cases l
  · rfl
  · simp [mk₁, extract, StackTape.mapSome, List.reduceOption]

end Retract

section Move

/--
Move the head left by shifting the left StackTape under the head.
-/
def moveLeft (t : BiTape Symbol) : BiTape Symbol :=
  ⟨t.left.head, t.left.tail, StackTape.cons t.head t.right⟩

/--
Move the head right by shifting the right StackTape under the head.
-/
def moveRight (t : BiTape Symbol) : BiTape Symbol :=
  ⟨t.right.head, StackTape.cons t.head t.left, t.right.tail⟩

/--
Move the head to the left or right, shifting the tape underneath it.
-/
def move (t : BiTape Symbol) : Dir → BiTape Symbol
  | .left => t.moveLeft
  | .right => t.moveRight

/--
Optionally perform a `move`, or do nothing if `none`.
-/
def optionMove : BiTape Symbol → Option Dir → BiTape Symbol
  | t, none => t
  | t, some d => t.move d

@[simp]
lemma moveLeft_moveRight (t : BiTape Symbol) : t.moveLeft.moveRight = t := by
  simp [moveRight, moveLeft]

@[simp]
lemma moveRight_moveLeft (t : BiTape Symbol) : t.moveRight.moveLeft = t := by
  simp [moveLeft, moveRight]

end Move

/--
Write a value under the head of the `BiTape`.
-/
def write (t : BiTape Symbol) (a : Option Symbol) : BiTape Symbol := { t with head := a }

/--
The space used by a `BiTape` is the number of symbols
between and including the head, and leftmost and rightmost non-blank symbols on the `BiTape`.
-/
@[scoped grind]
def spaceUsed (t : BiTape Symbol) : ℕ := 1 + t.left.length + t.right.length

@[simp, grind =]
lemma spaceUsed_write (t : BiTape Symbol) (a : Option Symbol) :
    (t.write a).spaceUsed = t.spaceUsed := by rfl

lemma spaceUsed_mk₁ (l : List Symbol) :
    (mk₁ l).spaceUsed = max 1 l.length := by
  cases l with
  | nil => simp [mk₁, spaceUsed, nil, StackTape.length_nil]
  | cons h t => simp [mk₁, spaceUsed, StackTape.length_nil, StackTape.length_mapSome]; omega

lemma spaceUsed_move (t : BiTape Symbol) (d : Dir) :
    (t.move d).spaceUsed ≤ t.spaceUsed + 1 := by
  cases d <;> grind [moveLeft, moveRight, move,
    spaceUsed, StackTape.length_tail_le, StackTape.length_cons_le]


section Nth

/-- The `nth` function of a tape is integer-valued, with index `0` being the head, negative indexes
on the left and positive indexes on the right. (Picture a number line.) -/
def nth (T : BiTape Symbol) : ℤ → Option Symbol
  | 0 => T.head
  | .ofNat (n + 1) => T.right.nth n
  | .negSucc n => T.left.nth n

@[ext]
/- Two BiTapes are equal if their `n`th tape symbol is equal for all `n ∈ ℤ`. -/
theorem ext_nth (T₁ T₂ : BiTape Symbol) :
    (∀ n, T₁.nth n = T₂.nth n) → T₁ = T₂ := by
  intro h
  rw [BiTape.mk.injEq]
  refine ⟨h 0, ?_, ?_⟩
  <;> apply StackTape.ext_nth
  <;> intro n
  · exact h (-(n + 1))
  · exact h (n + 1)

lemma moveLeft_nth (T : BiTape Symbol) (n : ℤ) :
    T.moveLeft.nth n = T.nth (n - 1) := by
  match n with
  | 0 =>
    rw [moveLeft, ← StackTape.nth_zero]
    rfl
  | .ofNat (n + 1) =>
    simp [nth, moveLeft]
    cases n
    <;> simp
  | .negSucc n =>
    simp [nth, moveLeft]

lemma moveRight_nth (T : BiTape Symbol) (n : ℤ) :
    T.moveRight.nth n = T.nth (n + 1) := by
  conv_rhs =>
    rw [← moveRight_moveLeft T, moveLeft_nth, add_sub_cancel_right]

def posChange : Option Dir → ℤ
  | some .left => -1
  | some .right => 1
  | none => 0

lemma optionMove_nth (T : BiTape Symbol) (dir : Option Dir) (n : ℤ) :
    (T.optionMove dir).nth n = T.nth (n + posChange dir) := by
  match dir with
  | none => simp [optionMove, posChange]
  | some .left => simp [optionMove, move, moveLeft_nth, posChange, Int.add_neg_one]
  | some .right => simp [optionMove, move, moveRight_nth, posChange]

lemma write_nth (T : BiTape Symbol) (n : ℤ) (a : Option Symbol) :
    (T.write a).nth n = if n = 0 then a else T.nth n := by
  match n with
  | 0 => rfl
  | .ofNat (n + 1) => rfl
  | .negSucc n => rfl

@[simp]
lemma mk₁_nth_nat (l : List Symbol) (n : ℕ) :
    (BiTape.mk₁ l).nth n = l[n]? := by
  cases l
  <;> cases n
  <;> simp [mk₁, nth, nil]

@[simp]
lemma mk₁_nth_int (l : List Symbol) (n : ℕ) :
    (BiTape.mk₁ l).nth (Int.negSucc n) = none := by
  cases l
  <;> simp [mk₁, nth, nil]

/-- The BiTape `T` only contains `none` symbols outside of the support set `S`. -/
def IsSupportedBy (T : BiTape Symbol) (S : Set ℤ) : Prop :=
  ∀ n ∉ S, T.nth n = default

/- Two BiTapes are equal if their `n`th tape symbols agree on a support set. -/
theorem ext_nth_SupportedBy {T₁ T₂ : BiTape Symbol} {S : Set ℤ} (h₁ : T₁.IsSupportedBy S)
    (h₂ : T₂.IsSupportedBy S) :
    (∀ n ∈ S, T₁.nth n = T₂.nth n) → T₁ = T₂ := by
  intro h
  apply ext_nth
  intro n
  by_cases hn : n ∈ S
  · exact h n hn
  · rw [h₁ n hn, h₂ n hn]

end Nth

end BiTape

end Turing
