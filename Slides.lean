import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

#doc (Slides) "Formalisation of Complexity theory" =>

# Formalisation of Complexity Theory

Building towards the Cook-Levin theorem

Design choices, Challenges & Current Progress

# What is computability (intuitively)?

* _Computabilty_ means _Solving things using effective procedures_
  * → Algorithms
* Anything a "modern-day computer" can solve / compute

# Defining computability
%%%
vertical := some true
%%%

* Coming up with a _mathematically precise_ definition is not easy.
* Many different, possible definitions
* Some questions to answer

## Model of computation
* Turing machines, variants thereof
* Finite automata
* Machine-based models
* λ-calculus
* Partially recursive functions
* General: Determinism of the chosen model

## Measuring Resources
* Execution time
* Space needed for computation
* Number of communications, queries
* Parallelism

## In-/Output
* Mathematical objects of interested need to be _encoded_
* Different possible ways to deal with Higher-Order functions
* Typically: Work with computations over alphabets:
  * An _alphabet_ $`Γ` is a finite set (thought of as symbols)
  * $`Γ^*` denotes the set of (finite) words consisting of letters in $`Γ`
  * Study functions $`f \colon Γ^* → Γ^*`
  * Recognize (i.e. decide membership) _languages_ $`L ⊆ Γ^*`

## Model of computation
:::class "definition"
*Definition (informal)*
A *Model of Computation* is a model that describes how output to a mathematical function is
computed giving an input.
It describes the "computation process" and may allow to measure resource consumption such as
time or space.
:::

# Objects of interest
%%%
vertical := some true
%%%

:::class "definition"
*Definition*
For a computational model, let `P` be the set of languages $`L ⊆ Γ^*` recognizable
in polynomial time, i.e. where the membership problem $`w ∈ L` is "computable" in polynomial time.
This means that there is a polynomial $`p(n)` and a "computer" $`τ` such that $`τ` can decide
$`w ∈ L` in time $`p(|w|)` for any $`w`, where $`|w|` denotes the length of a word.
:::

## Objects of interest

:::class "definition"
*Definition*
For a computational model, let `NP` be the set of languages $`L ⊆ Γ^*` verifiable in polynomial
time, i.e. there is a verification language $`V ⊆ L × Γ^*`such that
$$`w ∈ L ↔ ∃ c, (w, c) ∈ V`
and $`V` is recognizable in polynomial time wrt $`w`.
:::

## Other common complexity classes

* `EXPTIME`, the languages recognizable with exponential time $`O(2^(P(n)))`
* `NEXPTIME`, the languages recognizable with exponential time non-deterministically
* `PSPACE`, the languages recognizable with polynomial space
* `EXPSPACE`, the languages verifiable with polynomial space

:::class "theorem"
*Theorem*
`P ⊆ NP ⊆ PSPACE ⊆ EXPTIME ⊆ NEXPTIME ⊆ EXPSPACE`
:::

## Transformations between languages

:::class "definition"
*Definition*
We say that the language $`L₁ ⊆ Γ^*` *transforms (polynomially)* to the language $`L₂ ⊆ Σ^*`
if there is a function $`f : Γ^* → Σ^*` (computable in polynomial time) such that
$$` w ∈ L₁  ↔ f(w) ∈ L₂`
:::

## NP-Completeness

:::class "definition"
*Definition*
A language $`L` in `NP` is said to be `NP`-complete if every language $`L'` in `NP` transforms
to $`L` in polynomial time.
:::

:::::fragment
:::class "theorem"
*Theorem (Cook-Levin)*
The Boolean Satisfiability Problem `SAT` is an `NP`-complete problem.
:::
:::::

## Boolean Satisfiability
:::class "definition"
*Definition (SAT)*
A *Clause* is a list of boolean variables or negations thereof.
An *instance* of the Boolean Satisfiability Problem is a list of clauses.
It asks whether there is a truth assignment to the variables such that in every clause,
there is at least one true element (after applying the negations).
:::

:::::fragment
:::class "example"
*Example*
$$`(x_1 ∨ \overline{x_2} ∨ x_3) ∧ (\overline{x_1} ∨ x_2) ∧ (x_2 ∨ \overline{x_3})`
:::
:::::



# Turing Machines
%%%
vertical := some true
%%%

:::class "definition"
*Definition*
A (single tape) *Turing Machine* over the alphabet $`Γ` is a finite set $`S` of *States*
together with a starting state $`q_0 ∈ S` and a transition function
$$`\text{tr} : S × \underbrace{(Γ ∪ \{␣\})}_{\text{read}} → \underbrace{\{-1, 0, 1\}}_{\text{move}} × \underbrace{(Γ ∪ \{␣\})}_{\text{write}} × \underbrace{(S ∪ \{\text{HALT}\})}_{\text{new state}}.`
A *Tape* is a finite support function $`ℤ → Γ ∪ \{␣\}`.
A *Configuration* (of a TM) is a pair of $`s ∈ S ∪ \{\text{HALT}\}` and a tape.
:::

## Turing Machines : Computation

:::class "definition"
*Definition*
The *Computation* of a Turing Machine $`τ` on input of a word $`l ∈ Γ^*`
is the sequence $`(c_i)_{i ∈ ℕ}` of configurations defined recursively as follows:
The starting configuration $`c_0 := (q_0, T_0)` is the pair of
starting state and a tape initialized with $`l` on the nonnegative indices
(and blanks on the left/right).
The state $`c_{n + 1}` is obtained from $`c_n = (q_n, T_n)` as described by
$$`(m, w, q) := \text{tr}(q_n, (T_n(0))) ∈ \{-1, 0, 1\} × (Γ ∪ \{␣\}) × (S ∪ \{\text{HALT}\})`
That is, writing $`w`, shifting indices of $`T_n` by $`m` and transitioning to state $`q`.
:::

## Turing Machines : Output, computing functions
:::class "definition"
*Definition*
The computation of $`τ` on input $`l` *halts* after $`n` steps if $`q_n = \text{HALT}`.
We say that it *outputs* $`l'` if the tape $`T_n` contains $`l'` on the nonnegative indices
(and only blanks elsewhere).
The machine $`τ` is said to *compute* a function $`f : Γ^* → Γ^*` in time $`t : ℕ → ℕ`
if for every word $`l ∈ Γ^*`, the computation of $`τ` on input $`l` halts in at most
$`t ( \operatorname{len} (l))` steps and outputs $`f(l)`.
:::

## Multi-Tape Turing machines
:::class "definition"
*Definition (sketch)*
A Multitape Turing Machine is defined similar to a (singletape) Turing Machine, except
that it can work with a fixed finite amount of tapes. In one step of execution, every tape
can be read and written to, so the transition function becomes
$$`\text{tr} : S × \underbrace{(Γ ∪ \{␣\})^n}_{\text{read}} → \underbrace{\{-1, 0, 1\}}_{\text{move}} × \underbrace{(Γ ∪ \{␣\})^n}_{\text{write}} × \underbrace{(S ∪ \{\text{HALT}\})}_{\text{new state}}.`
:::

## Lean formalisation

Existing definitions in CSLib look as follows:

```leanLibCode -panel Cslib.Computability.Machines.SingleTapeTuring.Basic (decl := Turing.SingleTapeTM)
/--
A single-tape Turing machine
over the alphabet of `Option Symbol` (where `none` is the blank `BiTape` symbol).
-/
structure SingleTapeTM Symbol [Inhabited Symbol] [Fintype Symbol] where
  /-- type of state labels -/
  (State : Type)
  /-- finiteness of the state type -/
  [stateFintype : Fintype State]
  /-- Initial state -/
  (q₀ : State)
  /-- Transition function, mapping a state and a head symbol to a `Stmt` to invoke,
  and optionally the new state to transition to afterwards (`none` for halt) -/
  (tr : State → Option Symbol → SingleTapeTM.Stmt Symbol × Option State)
```

## Turing Machines : Configuration
```leanLibCode -panel Cslib.Computability.Machines.SingleTapeTuring.Basic (decl := Turing.SingleTapeTM.Cfg)
/--
The configurations of a Turing machine consist of:
an `Option`al state (or none for the halting state),
and a `BiTape` representing the tape contents.
-/
@[ext]
structure Cfg : Type where
  /-- the state of the TM (or none for the halting state) -/
  state : Option tm.State
  /-- the BiTape contents -/
  BiTape : BiTape Symbol
deriving Inhabited
```


## Turing Machines : Computation

```leanLibCode -panel Cslib.Computability.Machines.SingleTapeTuring.Basic (decl := Turing.SingleTapeTM.step)
/-- The step function corresponding to a `SingleTapeTM`. -/
--@[simp]
def step : tm.Cfg → Option tm.Cfg
  | ⟨none, _⟩ =>
    -- If in the halting state, there is no next configuration
    none
  | ⟨some q', t⟩ =>
    -- If in state q', perform look up in the transition function
    match tm.tr q' t.head with
    -- and enter a new configuration with state q'' (or none for halting)
    -- and tape updated according to the Stmt
    | ⟨⟨wr, dir⟩, q''⟩ => some ⟨q'', (t.write wr).optionMove dir⟩
```

## Turing Machines: In-/Output

```leanLibCode -panel -stretch Cslib.Computability.Machines.SingleTapeTuring.Basic (decl := Turing.SingleTapeTM.initCfg)
/--
The initial configuration corresponding to a list in the input alphabet.
Note that the entries of the tape constructed by `BiTape.mk₁` are all `some` values.
This is to ensure that distinct lists map to distinct initial configurations.
-/
def initCfg (tm : SingleTapeTM Symbol) (s : List Symbol) : tm.Cfg :=
  ⟨some tm.q₀, BiTape.mk₁ s⟩
```

```leanLibCode -panel -stretch Cslib.Computability.Machines.SingleTapeTuring.Basic (decl := Turing.SingleTapeTM.haltCfg)
/-- The final configuration corresponding to a list in the output alphabet.
(We demand that the head halts at the leftmost position of the output.)
-/
def haltCfg (tm : SingleTapeTM Symbol) (s : List Symbol) : tm.Cfg :=
  ⟨none, BiTape.mk₁ s⟩
```

# Formalising Cook-Levin
%%%
vertical := some true
%%%

* Suppose we are given a language $`L ⊆ Σ^*` that is in `NP`. We need to
* Proof that `SAT` is a problem `NP`
* Specify the transformation function $`f : L → \text{SAT}`
* Proof that $`f` is a transformation, i.e. preserves membership
* Proof that $`f` is computable in polynomial time

## Challenges in formalisation
* Specifying $`f` and proving that it is a transformation: doable (~2000 LOC)
* Proving `SAT` to be `NP` and proving $`f` to be (poly-time) computable: hard
  * Need to prove existence of Turing Machines, but "programming" there is tedious
* Better approach: Use a more expressive model of computation to give existence proofs
  * λ-calculus
  * Need notions of equivalence to "pull in" proofs from other models

# Models of computation
%%%
vertical := some true
%%%
* Need different notions of "equivalence" between computation models.
* Most common / useful for Cook-Levin: Equivalent up to polynomial time overhead
* Other applications will need space guarantees as well


## Equivalences of Models
* Turing Machine{fragment (style := highlightRed) (index := 2)}[s] are Model{fragment (style := highlightRed) (index := 2)}[s] of computation
* Many of these lead to the same notions of "computable", `P`, `NP`, `NP`-completeness, etc.
  * SingleTapeTM, SingleTapeTM (write _or_ move), MultiTapeTM, ...
* We already get different notions for questions like:
  * Is this function computable in $`O(n^2)`?
* Some notions are insensible:
  * Is this function computable with $`O(\operatorname{log} n)` space on a SingleTapeTM?


## Formalisation of Computation Models

```leanLibCode -panel -stretch Cslib.Computability.Machines.ComputationModel.Basic (decl := Computation.TransitionSystem)
/--
For each element `(t : τ)`, there is a bundle of a type `cfg t` with a step / transition function
`cfg t → Option (cfg t)`.
-/
class TransitionSystem (τ : Type u) where
  cfg (t : τ) : Type*
  red {t : τ} : cfg t → cfg t → Prop
```

```leanLibCode -panel -stretch Cslib.Computability.Machines.ComputationModel.Basic (decl := Computation.TransitionMachine)
/--
Bundles a `TransitionSystem` with input and output functions from/to words over an alphabet.
This way, we can think of elements of `τ` as allowing computations `List Γᵢ → List Γₒ`
by lifting inputs into the computation context, iterating the `step` function,
and taking output from this computation context.
-/
class TransitionMachine (τ : Type u) (Γᵢ Γₒ : outParam (Type v)) extends TransitionSystem τ where
  init {t : τ} : List Γᵢ → cfg t
  -- TODO: Potentially work with a partial function here instead of `Option`?
  output {t : τ} : cfg t → Option (List Γₒ)
```

## Turing machines as a Computation Model
```leanLibCode -panel -stretch Cslib.Computability.Machines.SingleTapeTuring.Basic (startLine := 249) (endLine := 253)
noncomputable instance : TransitionMachine (SingleTapeTM Symbol) Symbol Symbol where
  cfg := Cfg
  red {t} c c' := t.step c = some c'
  init {t} := initCfg t
  output := extractOutput
```

```leanLibCode -panel Cslib.Computability.Machines.ComputationModel.Basic (decl := Computation.TransitionMachine.OutputsInTime)
/--
The transition machine `t` outputs `l'` on input `l` in at most `n` steps.
-/
structure OutputsInTime (t : τ) (n : ℕ) (l : List Γᵢ) (l' : List Γₒ) where
  haltState : (cfg t)
  haltState_halts : ¬ ∃ s, red haltState s
  evals_to : TransitionSystem.EvalsToInTime t (init l) haltState n
  output_eq : output haltState = some l'
```

# Future Work: Formal Programming Language
* λ-calculus _better suited_ than Turing Machines, but still not easy to "program"
* Would like: Formal programming language that "compiles to" λ-calculus:
  * High-level, expressive
  * Easy to verify
  * How much fine-tunable semantics to control e.g. memory space?


# References
* The CSLib project: [github.com/leanprover/cslib](https://github.com/leanprover/cslib)
* Mechanising Complexity Theory: The Cook-Levin Theorem in Coq. Lennard Gäher, Fabian Kunze. [ITP 2021 files](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2021.20)



# Slides / Resources
* Slides available at [maximilian-kessler.de/complexity-theory-slides-1](https://maximilian-kessler.de/complexity-theory-slides-1)
* My fork of CSLib: [git.abstractnonsen.se/max/cslib](https://git.abstractnonsen.se/max/cslib)
  * Check out the branches (mostly `computation-model-typeclasess`) for my code
  * Code for these slides in branch `talk-1`
* Follow development / discussions: `#cslib` channel in the leanprover community Zulip
