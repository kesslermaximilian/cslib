import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

#doc (Slides) "Formalisation of Complexity theory" =>

# Formalisation of Complexity Theory

Building towards the Cook-Levin theorem

Design choices, Challenges & Current Progress

# What is computability (intuitively)?

* _Computabilty_ means _Solving things using effective procedures_
  * _Algorithms_
* Anything a "modern-day computer" can solve / compute

# Defining computability
%%%
vertical := some true
%%%

* Coming up with a _mathematically precise_ definition is not easy.
* Many different, possible definitions

## Model of computation
* Turing machines, variants thereof
* Finite automata
* Machine-based models
* λ-calculus
* Partially recursive functions

## Measuring Resources
* Execution time
* Space needed for computation
* Number of communications, queries
* Parallelism

## In-/Output
* Mathematical objects of interested need to be _encoded_
* Typically: Work with computations over alphabets
  * $`f \colon Γ^* → Γ^*`
* Different possible ways to deal with Higher-Order functions


# Turing Machines
%%%
vertical := some true
%%%

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


# Things of interest

## computable
A thing is computable iff

### this is a test

:::class "theorem"
some theorem
:::
