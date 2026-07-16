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
to $`L` polynomially
:::

:::class "theorem"
*Theorem (Cook-Levin)*
The Boolean Satisfiability Problem `SAT` is an `NP`-complete problem.
:::


# Turing Machines
%%%
vertical := some true
%%%

:::class "definition"
*Definition*
A (single tape) *Turing Machine* over the alphabet $`Γ` is a finite set $`S` of *States*
together with a starting state $`q_0 ∈ S` and a transition function
$$`\text{tr} : S → \underbrace{(Γ ∪ \{␣\})}_{\text{read}} → \underbrace{\{-1, 0, 1\}}_{\text{move}} × \underbrace{(Γ ∪ \{␣\})}_{\text{write}} × \underbrace{(S ∪ \{\text{HALT}\})}_{\text{new state}}.`
A *Tape* is a finite support function $`ℤ → Γ ∪ \{␣\}`.
A *Configuration* (of a TM) is a pair of $`s ∈ S ∪ \{\text{HALT}\}` and a tape.
:::

## Turing Machines : Computation

:::class "definition"
*Definition*
The *Computation* of a Turing Machine $`τ` on input of a word $`l ∈ Γ^*`
is the sequence $`(c_i)_{i ∈ ℕ}` of configurations defined recursively as follows:
The starting configuration $`c_0 := (q_0, T_0)` is the pair of
starting state and a tape initialized with `l` on the nonnegative indices (and blanks on the left/right).
The state $`c_{n + 1}` is obtained from $`c_n = (q_n, T_n)` as described by
$$`(m, w, q) := \text{tr}(q_n, (T_n(0))) ∈ \{-1, 0, 1\} × (Γ ∪ \{␣\}) × (S ∪ \{\text{HALT}\}).`
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

## Lean definition

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

```leanLibCode -panel Cslib.Computability.Machines.SingleTapeTuring.Basic (decl := Turing.SingleTapeTM.haltCfg)
/-- The final configuration corresponding to a list in the output alphabet.
(We demand that the head halts at the leftmost position of the output.)
-/
def haltCfg (tm : SingleTapeTM Symbol) (s : List Symbol) : tm.Cfg :=
  ⟨none, BiTape.mk₁ s⟩
```
