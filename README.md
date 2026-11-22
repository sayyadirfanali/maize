# Maize

Maize is a small library written in [Lean 4](https://lean-lang.org) that gives decision tables a precise, generalised denotational semantics and uses it to check tables for conflicting rules before they run.
It derives both [DMN](https://www.omg.org/dmn/) and [DWDS](https://xalgorithms.org/) as instances of a single core model.

## What is a Decision Table?

A decision table encodes conditional rules as a grid rather than nested `if`–`then` statements.
In the most common layout (used by DMN), each column represents an input condition or an output answer, and each row represents one rule saying "if every input condition holds, produce this answer" (other formats, such as DWDS, transpose the grid so each rule is a column).
For example, a venue might set ticket prices by age using two rules:

| Rule | Age | Price |
| :--- | :--- | :--- |
| 1 | 12 or under | 5 |
| 2 | 12 or over | 10 |

To use the table, take the observed facts (say, a visitor aged 30), find every rule whose conditions match those facts (Rule 2), and read off the resulting price (`10`).
Organisations use tables like this to express pricing tiers, loan eligibility, welfare benefits, and trade regulations, often with dozens or hundreds of rules.

## Why Formalise?

In the ticket table above, a 12-year-old matches both "12 or under" and "12 or over", yielding two conflicting prices (`5` and `10`).
Unit tests catch an overlap like that only if someone thinks to test the exact colliding combination of inputs, and in realistic multi-column tables over unbounded numbers and text, testing every input is impossible.

Giving decision tables a formal **denotational semantics**—defining what a table means as a mathematical relation before writing execution or analysis code—buys four things that testing alone cannot:

1. **Unambiguous specifications:** Prose standards inevitably leave corner cases open; writing the semantics in Lean forces every case to be made explicit (surfacing several open questions in DWDS documented in [`OPEN_QUESTIONS.md`](OPEN_QUESTIONS.md)).
2. **Verified conflict search and universal safety:** Maize builds an executable conflict finder (`Table.findConflict`) proved both *sound* (any input it reports genuinely triggers a conflict) and *complete* (when it finds nothing, **no input** in the modelled domain can ever trigger one).
3. **Provably correct evaluators:** Reference evaluators are proved to agree with the mathematical specification, ruling out engine bugs.
4. **Safe transformations and translations:** Defining equivalence mathematically (`Table.Equiv`) lets Maize prove when reordering rules, deduplicating rows, merging rule sets, or translating between formats preserves table behaviour.

## DMN

Decision Model and Notation ([DMN](https://www.omg.org/dmn/), maintained by the Object Management Group) is the industry standard for business decision tables (`Maize/DMN.lean`).
Evaluating a DMN table happens in two distinct steps—first **matching** individual rows, and then **picking** a final answer from whichever rows matched:

1. **Matching cells (`DMN.Test`):** Inputs in Maize's DMN model are integers, strings, or booleans (`DMN.Value`).
Each input cell in a row holds a test on that column's input—such as an exact match, a comparison (`<= 12`), an open or closed integer range (`[12..64]`), a list of allowed values, or `-` (which accepts any value).
A row matches an input when every cell in that row passes its test.
2. **Picking results (`DMN.Pick`):** Because several rows can match the same input at once, every DMN decision table declares a **hit policy** saying how to resolve multiple matches:
   - **unique (`U`):** at most one row may match; if two or more rows match, evaluation fails with an error (called a *violation*).
   - **any (`A`):** multiple rows may match only if they all give the exact same output; if they disagree, evaluation fails with a violation.
   - **first (`F`):** return the output of the first matching row from the top of the table, ignoring later matches.
   - **collect (`C`):** return a list of outputs from all matching rows, without treating row order as meaningful.
   - **rule order (`R`):** like collect, returning the outputs of all matching rows in top-to-bottom order.

### Example 1: ticket prices

Consider the faulty ticket table written in DMN under the **unique** policy (`DMN.ticketBuggy`):

| Rule | Age | Price |
| :--- | :--- | :--- |
| 1 | `<= 12` | `5` |
| 2 | `>= 12` | `10` |

Instead of guessing test inputs, Maize converts each cell's test into a normalised interval or value list (`DMN.Shape`) and intersects them column by column.
Searching `DMN.ticketBuggy` automatically finds the overlap and returns age `12` (`DMN.ticketBuggy_conflict`), where evaluation indeed fails with a violation.
Changing the first row from `<= 12` to `< 12` gives `DMN.ticketFixed`: the search now finds nothing, proving that no visitor age will ever cause a violation (`DMN.ticketFixed_never_violates`).

### Example 2: four-column freight surcharges

Boundary-value testing on a single column might easily try `12`, `1000`, or `50000` in isolation; the real hazard in multi-column tables is an unintended combination across several columns at once.
`DMN.freightBuggy` defines five surcharge rules across four inputs—weight, declared value, destination region, and hazardous goods—where two rules look separate at a glance, yet an off-by-one (`< 50001` instead of `< 50000`) makes them collide:

- Maize proves that the two rules match together **at one shipment and no other** across all integers, strings, and booleans: `1000` kg, declared value `50000`, region `"APAC"`, hazardous (`DMN.freight_overlap_exactly`).
- Running `DMN.findUniqueConflict` automatically extracts those two rules and that exact four-field shipment (`DMN.freightBuggy_conflict`).
- Fixing `< 50001` to `< 50000` (`DMN.freightFixed`) makes the search return nothing, proving that *no* shipment ever causes a violation (`DMN.freightFixed_never_violates`).

Maize also checks a customer discount table over arbitrary customer names and order sizes (`DMN.discount_never_violates`), and reproduces the loan-grade table from Table 1 of Calvanese et al., ["Semantics and Analysis of DMN Decision Tables"](https://arxiv.org/abs/1603.07466) (BPM 2016) (`DMN.loanGrade`), confirming both the rule overlap (`DMN.loanGrade_not_unique`) and the uncovered applicant gap (`DMN.loanGrade_gap`) reported in the paper.

### Theorems Proved for DMN

- **Exact overlap checking (`DMN.Test.overlap_iff`):** two S-FEEL tests share a passing value if and only if the intersection of their normalised shapes is non-empty, turning a question over infinitely many integers and strings into an exact check.
- **Soundness and completeness of `unique` search (`DMN.findUniqueConflict_sound`, `DMN.findUniqueConflict_none_never_violates`):** if `DMN.findUniqueConflict` returns an input, evaluating the table there under **unique** really produces a violation; if it returns nothing, the table satisfies `DMN.Unique` and *never* produces a violation for any input (`DMN.eval_unique_ne_violation`).
- **Soundness of `any` (`DMN.eval_any_ne_violation`):** if matching rows never disagree on their outputs (`DMN.AnyValid`) and every output cell is filled, evaluating under **any** never produces a violation.
- **Order sensitivity of `first` (`DMN.first_depends_on_order`):** under **first**, moving a row to the top of the table can change the answer.

## DWDS

The [Data With Direction Specification](https://gitlab.com/xalgorithms-alliance/data-with-direction-specification/dwds-documents/-/tree/master/current) (DWDS), developed by [Xalgorithms](https://xalgorithms.org/) and detailed in Joseph Potvin's 2023 DBA thesis, is a tabular rule format designed for trade, tax, and regulatory rules (`Maize/DWDS.lean`).
Unlike DMN, DWDS writes each rule—called a **scenario**—as a column rather than a row, and is built for situations where facts may be incomplete and conflicting rules require human judgment rather than an automated tie-breaker:

1. **Four-valued conditions (`DWDS.State`):** Both the cells in a scenario and the observed facts take one of four states: `YES`, `NO`, `YES-OR-NO` (meaning "either way" in a rule, or "not yet known" in a fact), and `YES-AND-NO` (a conflicted "both" state).
When matching a scenario against observed facts (`DWDS.hit`), everything matches everything *except* `YES` against `NO` and `NO` against `YES` (whether `YES-AND-NO` matches `YES-OR-NO` is left unstated in the thesis and marked provisional in the code).
2. **Obligation modes and human choice (`DWDS.Mode`):** Instead of returning numbers or text, each output row expresses whether an action **MUST**, **MAY**, or **SHOULD** happen—or **NOT**, which simply means this scenario says nothing about that action.
DWDS has no hit policy that discards rows or throws errors: all matching scenarios contribute their answers, and if two matching scenarios give different modes for the same action (such as `MUST` and `MAY`), the decision is **deferred** (`Table.Deferred`) to a person.

### Example 1: notifying the stevedore

Consider a two-scenario gate (`DWDS.mini`) deciding whether to notify a stevedore, depending on whether a shipping container is loaded and locked (written with scenarios as columns):

| | Scenario 1 | Scenario 2 |
| :--- | :--- | :--- |
| **Loaded** (input) | `YES` | `YES-OR-NO` |
| **Locked** (input) | `YES-OR-NO` | `YES` |
| **Notify stevedore** (output) | `MUST` | `MAY` |

If the container is loaded (`YES`) and not locked (`NO`), only Scenario 1 matches, so the answer is `MUST` (`DWDS.mini_one`).
If it is both loaded (`YES`) and locked (`YES`), both scenarios match and assert `MUST` and `MAY`, leaving the decision to a person (`DWDS.mini_deferred`)—a situation Maize's conflict search finds on its own (`DWDS.mini_choice`).

### Example 2: container (Potvin's thesis)

Maize encodes the full eight-scenario shipping container gate from Figure 28 of Potvin's thesis (`DWDS.container`, which controls green, yellow, and red signal lights alongside stevedore and insurance notifications) and reproduces the worked examples from Figures 30 and 31 (`DWDS.exampleA`, `DWDS.exampleB`).
Searching across all definite (`YES`/`NO`) facts proves that the green, yellow, and red lights never require a human decision (`DWDS.container_decisive_green`, `DWDS.container_decisive_yellow`, `DWDS.container_decisive_red`), while uncovering a stevedore choice point—when a container is not loaded, not inspected, and locked (`DWDS.container_stevedore_choice`)—that the thesis's worked figures do not show, alongside the insurance conflict (`DWDS.container_insurance_choice`).
Because conflicts are checked one output row at a time, Maize also shows that in Figure 31 both the green light and the red light are individually unambiguous (`MUST`) at the same time (`DWDS.exampleB_green_and_red`).

Questions the formalisation raised about DWDS—including `YES-AND-NO` against `YES-OR-NO`, whether `NOT` always means silence, simultaneous green and red lights, and Rule 256—are documented in [`OPEN_QUESTIONS.md`](OPEN_QUESTIONS.md).

### Theorems Proved for DWDS

- **Finding every human choice point (`DWDS.decisive_iff`, `DWDS.definiteSampler`):** when observed facts are definite (`YES` or `NO`), two scenarios can match together if and only if no condition has `YES` in one and `NO` in the other, allowing `Table.findConflict` to find every output where a person might have to decide.
(Without restricting to definite facts, an all-`YES-OR-NO` input matches every scenario at once: `DWDS.coInvocable_any`.)
- **Compatibility with ordinary Boolean tables (`DWDS.ought_toDWDS`):** reading an ordinary yes/no table as a DWDS gate (`Table.toDWDS`) produces the exact same answers on yes/no facts.
- **Precision and non-transitivity (`DWDS.refines_yesOrNo`, `DWDS.hit_not_trans`):** replacing `YES-OR-NO` with `YES` or `NO` refines the facts (and therefore never creates a new conflict), while matching itself is reflexive and symmetric but not transitive (`YES` matches `YES-OR-NO` and `YES-OR-NO` matches `NO`, yet `YES` misses `NO`).

## Catch-All Rules: "Otherwise" or "Also"?

Rule authors often add a final **catch-all** rule—a row of `-` in DMN or a column of `YES-OR-NO` in DWDS—intending it to mean *"otherwise, use this default"*.
Because a catch-all cell actually means "match every value" (`Logic.Universal`), whether it behaves as "otherwise" or "also" depends entirely on how matching rules are combined.

In `DMN.ticketWithDefault`, adding a catch-all price of `8` beneath `< 12 → 5` and `[12..64] → 10` means a 70-year-old matches only row 3, while a 30-year-old matches both rows 2 and 3 (`DMN.ticketWithDefault_picks`):

- **unique and any:** the 30-year-old gets a violation.
- **collect and DWDS:** the catch-all means *"also"*—the 30-year-old gets both `10` and `8`, and adding a catch-all yellow light to the DWDS container gate turns on green, yellow, and red lights together (`DWDS.exampleB_withDefault`).
- **first:** the 30-year-old pays `10` and the 70-year-old pays `8`; only here does the catch-all mean *"otherwise"*.

Maize proves both rules in general: a catch-all that disagrees with any reachable rule always causes a conflict (`Table.not_decisive_of_catchAll`), except under DMN's **first** policy when placed at the very end of the table (`DMN.eval_first_catchAll`).

## The General Model

Both DMN and DWDS are instances of `Maize/Core.lean`, built around four main types (see [Terminology](#terminology) below for how Maize's core concepts connect to DMN and DWDS):

- `Logic`: specifies what a cell can expect, what a fact can be, what an output answer looks like, when a fact matches a cell (`hit`), and which output represents "no assertion" (`absent`).
- `Clause`: one rule (a row in DMN, a column in DWDS).
- `Table`: a list of clauses.
- `Is`: the observed facts, one per condition.

A clause is invoked (`Clause.Invoked`) when every cell matches its observed fact, and `Table.Ought` holds when some invoked clause asserts a non-absent answer.
For any input and output, `Table.trichotomy` proves that a table gives either no answer (`Table.Silent`), one unambiguous answer (`Table.Determinate`), or conflicting answers (`Table.Deferred`).
In programming-language terms, `Table.Ought` is a **denotational semantics**—the meaning of a table is a mathematical relation—and an executable evaluator (`Table.execute`) is proved to compute it (`Table.mem_execute`).

To get an automatic conflict search (`Table.findConflict`), a format only needs to supply one small helper, a `Logic.Sampler`, that picks a single fact accepted by two cells whenever one exists (in DMN by sampling intersected shapes, and in DWDS by picking `YES` or `NO`).

### Theorems Proved for Generalised Decision Tables

- **Universal conflict search (`Table.findConflict_sound`, `Table.findConflict_none`):** if `Table.findConflict` reports an input, the table genuinely conflicts there; if it reports nothing, the output is conflict-free (`Table.Decisive`) across *all* valid inputs.
- **Conflicts always come from pairs (`Table.not_decisive_iff`, `Clause.coInvocable_iff`):** any conflict comes from two disagreeing rules that can match together, and checking whether two rules can match together breaks down independently column by column.
- **Learning more facts never creates a conflict (`Table.Deferred.of_refines`):** replacing vague facts with more precise ones (`Is.Refines`) can resolve a conflict or leave a table silent, but can never create a new conflict.
- **Reordering, repeating, and merging rules (`Table.ought_perm`, `Table.ought_cons_of_mem`, `Table.append_comm`):** before any order-dependent hit policy is applied, reordering rules, repeating an existing rule, or merging tables in any order leaves `Table.Ought` unchanged, as do structure-preserving column renamings (`Table.ought_comap`) and format translations (`Table.ought_map`).

## Terminology

| Maize (`Core.lean`) | DMN (`DMN.lean`) | DWDS (`DWDS.lean`) |
| :--- | :--- | :--- |
| `Table` | Decision table | Logic gate |
| `Clause` | Rule (row) | Scenario (column) |
| `Condition` | Input column | Input condition |
| `Assertion` | Output column | Output assertion |
| `Logic.Expected` | Unary test (`DMN.Test`) | Input state (`00`, `01`, `10`, `11` in `DWDS.State`) |
| `Logic.Observed` | Input value (`DMN.Value`) | Observed state in `[is.dwd]` (`DWDS.State`) |
| `Logic.Mode` | Output value (`Option DMN.Value`) | Mode (`NOT`, `MUST`, `MAY`, `SHOULD` in `DWDS.Mode`) |
| `Logic.hit` | Value passes test (`DMN.passes`) | Hit / miss (`DWDS.hit`) |
| `Logic.absent` | No output (`none`) | `NOT` (`00`, `DWDS.Mode.not`) |
| `Clause.Invoked` | Rule matches | Scenario is invoked |
| `Table.Ought` | Unordered matching outputs | `[ought2.dwd]` result |
| `Table.Deferred` | Conflict (violation under `U`/`A`) | Choice point left to a person |
| `Logic.Sampler` | Shape overlap sampler (`DMN.sampler`) | Definite `YES`/`NO` sampler (`DWDS.definiteSampler`) |
| `DMN.Pick` | Hit policy (`U`, `A`, `F`, `C`, `R`) | *(None: all results kept)* |

## What Tests Don't Do

A unit test checks finitely many inputs on one table.
Maize's results fall into three tiers, the first two of which no finite test suite can establish:

1. **Proofs about every table and every input:** general theorems such as `Table.findConflict_sound`, `Table.findConflict_none`, `Table.Deferred.of_refines`, and `DMN.eval_unique_ne_violation`, which hold for arbitrary tables.
2. **Proofs about every input of one specific table:** universal guarantees established for a concrete table, such as `DMN.freightFixed_never_violates` (no shipment ever causes a violation), `DMN.freight_overlap_exactly` (the two buggy freight rules collide at *only* one four-tuple), and `DWDS.container_decisive_green` (no definite facts ever make the green light ambiguous).
3. **Checked examples on specific inputs:** theorems such as `DWDS.exampleA` and `DWDS.exampleB` (Figures 30 and 31 of Potvin's thesis), which confirm that the formal definitions match published examples.

Here "every input" means every value of the types Maize models: unbounded integers, strings, and booleans in DMN, and the four states in DWDS.

## Not Covered

- **DMN:** negated tests (`not(…)`), decimals, dates and times, missing/`null` inputs, the `priority` and `output order` hit policies, `collect` aggregation (`sum`, `count`, …), and default outputs.
- **DWDS:** Maize models only the `invoked` stage of a DWDS logic gate (matching scenarios to facts), not deciding which rules are `in effect` or `applicable`, multi-table pipelines, or exact-match readings of Rule 256.
- **File parsing:** neither DMN XML nor DWDS `.dwd` files are read; tables are written directly in Lean.

## Building

Requires [Lean 4](https://lean-lang.org) (via `elan`) and [Mathlib](https://github.com/leanprover-community/mathlib4):

```bash
lake exe cache get
lake build
```

## How This Was Made

I designed the model and the semantics, including what a table means, what to prove, and how to read DMN and DWDS into a generalised table.
I wrote a few core proofs myself, and used Claude and Gemini to help draft several other proofs and examples. Claude and Gemini also helped in drafting this README.
I personally audited every definition and theorem statement to verify that they faithfully capture the intended semantics (proof correctness is obviously guaranteed by the Lean kernel).

## Contact

Irfan Ali | [irfan@irfanali.org](mailto:irfan@irfanali.org)
