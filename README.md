# Maize

Maize is a small library in [Lean 4](https://lean-lang.org). It gives decision tables a precise, generalised denotational semantics.

It uses that semantics to check tables for conflicting rules before they run. Both [DMN](https://www.omg.org/dmn/) and [DWDS](https://xalgorithms.org/) are derived as instances of one core model.

## What is a Decision Table?

A decision table encodes conditional rules as a grid instead of nested `if`–`then` statements.

In DMN's layout, each column is an input condition or an output answer. Each row is one rule: "if every input condition holds, produce this answer." Other formats, such as DWDS, transpose the grid so each rule is a column.

For example, a venue might set ticket prices by age using two rules:

| Rule | Age | Price |
| :--- | :--- | :--- |
| 1 | 12 or under | 5 |
| 2 | 12 or over | 10 |

To use the table, take the observed facts (say, a visitor aged 30). Find every rule whose conditions match those facts (Rule 2), and read off the price (`10`).

Organisations use tables like this for pricing tiers, loan eligibility, welfare benefits, and trade regulations. Real tables often have dozens or hundreds of rules.

## Why Formalise?

In the ticket table above, a 12-year-old matches both rules and gets two conflicting prices (`5` and `10`).

Unit tests catch an overlap like that only if someone thinks to test age `12`. In large multi-column tables over unbounded numbers and text, testing every input is impossible.

Giving decision tables a formal **denotational semantics** defines what a table means as a mathematical relation before writing any execution or analysis code. This buys four things that testing alone cannot:

1. **Unambiguous specifications:** Prose standards leave corner cases open. Writing the semantics in Lean forces every case into the open (see [`OPEN_QUESTIONS.md`](OPEN_QUESTIONS.md) for questions raised about DWDS).
2. **Verified conflict search and universal safety:** Maize builds an executable conflict finder (`Table.findConflict`) proved both *sound* and *complete*. Any input it reports genuinely triggers a conflict. When it finds nothing, **no input** in the modelled domain can trigger one.
3. **Provably correct evaluators:** Reference evaluators are proved to agree with the mathematical specification, ruling out engine bugs.
4. **Safe transformations and translations:** Defining equivalence mathematically (`Table.Equiv`) lets Maize prove when reordering rules, deduplicating rows, merging rule sets, or translating between formats preserves table behaviour.

## DMN

Decision Model and Notation ([DMN](https://www.omg.org/dmn/), maintained by the Object Management Group) is the industry standard for business decision tables (`Maize/DMN.lean`).

Evaluating a DMN table takes two steps: first **matching** individual rows, and then **picking** a final answer from the matching rows.

1. **Matching cells (`DMN.Test`):**
   - Inputs in Maize's DMN model are integers, strings, or booleans (`DMN.Value`).
   - Each input cell holds a test on that column's input, such as an exact match, a comparison (`<= 12`), an integer range (`[12..64]`), a list of allowed values, or `-` (which accepts any value).
   - A row matches an input when every cell in that row passes its test.
2. **Picking results (`DMN.Pick`):** Because several rows can match the same input, every DMN table declares a **hit policy** saying how to combine them:
   - **unique (`U`):** at most one row may match. If two or more match, evaluation fails with a *violation*.
   - **any (`A`):** multiple rows may match only if they give the exact same output. If they disagree, evaluation fails with a violation.
   - **first (`F`):** return the output of the first matching row from the top of the table, ignoring later matches.
   - **collect (`C`):** return a list of outputs from all matching rows, ignoring row order.
   - **rule order (`R`):** return the outputs of all matching rows in top-to-bottom order.

### Example 1: ticket prices

Consider the faulty ticket table written in DMN under the **unique** policy (`DMN.ticketBuggy`):

| Rule | Age | Price |
| :--- | :--- | :--- |
| 1 | `<= 12` | `5` |
| 2 | `>= 12` | `10` |

Instead of guessing test inputs, Maize converts each cell's test into a normalised interval or value list (`DMN.Shape`). It then intersects them column by column.

Searching `DMN.ticketBuggy` finds the overlap and returns age `12` (`DMN.ticketBuggy_conflict`), where evaluation fails with a violation.

Changing the first row from `<= 12` to `< 12` gives `DMN.ticketFixed`. The search now finds nothing, proving that no visitor age will ever cause a violation (`DMN.ticketFixed_never_violates`).

### Example 2: four-column freight surcharges

Boundary-value testing on one column might easily try `12`, `1000`, or `50000` in isolation. The real hazard in multi-column tables is an unintended combination across several columns at once.

`DMN.freightBuggy` defines five surcharge rules across four inputs: weight, declared value, destination region, and hazardous goods. Two rules look separate at a glance, yet an off-by-one (`< 50001` instead of `< 50000`) makes them collide:

1. Maize proves that the two rules match together **at one shipment and no other** across all integers, strings, and booleans: `1000` kg, declared value `50000`, region `"APAC"`, hazardous (`DMN.freight_overlap_exactly`).
2. Running `DMN.findUniqueConflict` extracts those two rules and that exact four-field shipment (`DMN.freightBuggy_conflict`).
3. Fixing `< 50001` to `< 50000` (`DMN.freightFixed`) makes the search return nothing. This proves that *no* shipment ever causes a violation (`DMN.freightFixed_never_violates`).

Maize also checks a customer discount table over arbitrary names and order sizes (`DMN.discount_never_violates`).

It also reproduces the loan-grade table from Table 1 of Calvanese et al., ["Semantics and Analysis of DMN Decision Tables"](https://arxiv.org/abs/1603.07466) (BPM 2016) (`DMN.loanGrade`). This confirms both the rule overlap (`DMN.loanGrade_not_unique`) and the uncovered applicant gap (`DMN.loanGrade_gap`) reported in the paper.

### Theorems Proved for DMN

1. **Exact overlap checking (`DMN.Test.overlap_iff`):** two S-FEEL tests share a passing value if and only if the intersection of their normalised shapes is non-empty. This turns a question over infinitely many integers and strings into an exact check.
2. **Soundness and completeness of `unique` search (`DMN.findUniqueConflict_sound`, `DMN.findUniqueConflict_none_never_violates`):** if `DMN.findUniqueConflict` returns an input, evaluating the table there under **unique** produces a violation. If it returns nothing, the table satisfies `DMN.Unique` and *never* violates for any input (`DMN.eval_unique_ne_violation`).
3. **Soundness of `any` (`DMN.eval_any_ne_violation`):** suppose matching rows never disagree on their outputs (`DMN.AnyValid`) and every output cell is filled. Then evaluating under **any** never produces a violation.
4. **Order sensitivity of `first` (`DMN.first_depends_on_order`):** under **first**, moving a row to the top of the table can change the answer.

## DWDS

The [Data With Direction Specification](https://gitlab.com/xalgorithms-alliance/data-with-direction-specification/dwds-documents/-/tree/master/current) (DWDS), developed by [Xalgorithms](https://xalgorithms.org/) and detailed in Joseph Potvin's 2023 DBA thesis, is a tabular rule format for trade, tax, and regulatory rules (`Maize/DWDS.lean`).

Unlike DMN, DWDS writes each rule—called a **scenario**—as a column rather than a row. It is built for cases where facts may be incomplete and conflicting rules require human judgment rather than an automated tie-breaker:

1. **Four-valued conditions (`DWDS.State`):**
   - Both scenario cells and observed facts take one of four states: `YES`, `NO`, `YES-OR-NO` ("either way" in a rule, or "not yet known" in a fact), and `YES-AND-NO` (a conflicted "both" state).
   - Under `DWDS.hit`, everything matches everything *except* `YES` against `NO` and `NO` against `YES`. Whether `YES-AND-NO` matches `YES-OR-NO` is unstated in the thesis and marked provisional in the code.
2. **Obligation modes and human choice (`DWDS.Mode`):**
   - Instead of returning numbers or text, each output row states whether an action **MUST**, **MAY**, or **SHOULD** happen—or **NOT** (equivalent to `absent`).
   - DWDS has a no hit policy that discards rows or throws errors. All matching scenarios contribute their answers.
   - If two matching scenarios disagree on an action (such as `MUST` and `MAY`), the decision is **deferred** (`Table.Deferred`) to a person.

### Example 1: notifying the stevedore

Consider a two-scenario gate (`DWDS.mini`) deciding whether to notify a stevedore based on whether a shipping container is loaded and locked (written with scenarios as columns):

| | Scenario 1 | Scenario 2 |
| :--- | :--- | :--- |
| **Loaded** (input) | `YES` | `YES-OR-NO` |
| **Locked** (input) | `YES-OR-NO` | `YES` |
| **Notify stevedore** (output) | `MUST` | `MAY` |

If the container is loaded (`YES`) and not locked (`NO`), only Scenario 1 matches, so the answer is `MUST` (`DWDS.mini_one`).

If it is both loaded (`YES`) and locked (`YES`), both scenarios match and assert `MUST` and `MAY`. This leaves the decision to a person (`DWDS.mini_deferred`).

Maize's conflict search finds this situation on its own (`DWDS.mini_choice`).

### Example 2: container (Potvin's thesis)

Maize encodes the eight-scenario shipping container gate from Figure 28 of Potvin's thesis (`DWDS.container`). It controls green, yellow, and red signal lights alongside stevedore and insurance notifications.

It also reproduces the worked examples from Figures 30 and 31 (`DWDS.exampleA`, `DWDS.exampleB`).

Searching across all definite (`YES`/`NO`) facts proves that the green, yellow, and red lights never require a human decision (`DWDS.container_decisive_green`, `DWDS.container_decisive_yellow`, `DWDS.container_decisive_red`).

It also uncovers a stevedore choice point (`DWDS.container_stevedore_choice`) when a container is not loaded, not inspected, and locked, alongside the Figure 31 insurance conflict (`DWDS.container_insurance_choice`).

Conflicts are checked one output row at a time. Because of this, Maize also shows that in Figure 31 both the green light and the red light are individually unambiguous (`MUST`) at the same time (`DWDS.exampleB_green_and_red`).

Questions the formalisation raised about DWDS are documented in [`OPEN_QUESTIONS.md`](OPEN_QUESTIONS.md). These cover `YES-AND-NO` against `YES-OR-NO`, whether `NOT` always means silence, simultaneous green and red lights, and Rule 256.

### Theorems Proved for DWDS

- **Finding every human choice point (`DWDS.decisive_iff`, `DWDS.definiteSampler`):** when observed facts are definite (`YES` or `NO`), two scenarios can match together if and only if no condition has `YES` in one and `NO` in the other. This allows `Table.findConflict` to find every output where a person might have to decide.
- **Compatibility with ordinary Boolean tables (`DWDS.ought_toDWDS`):** reading an ordinary yes/no table as a DWDS gate (`Table.toDWDS`) produces the exact same answers on yes/no facts.
- **Precision and non-transitivity (`DWDS.refines_yesOrNo`, `DWDS.hit_not_trans`):** replacing `YES-OR-NO` with `YES` or `NO` refines the facts and never creates a new conflict. Matching itself is reflexive and symmetric, but not transitive (`YES` matches `YES-OR-NO` and `YES-OR-NO` matches `NO`, yet `YES` misses `NO`).

## Catch-All Rules: "Otherwise" or "Also"?

Rule authors often add a final **catch-all** rule—a row of `-` in DMN or a column of `YES-OR-NO` in DWDS—intending it to mean *"otherwise, use this default"*.

A catch-all cell actually means "match every value" (`Logic.Universal`). Whether it behaves as "otherwise" or "also" therefore depends on how matching rules are combined.

In `DMN.ticketWithDefault`, adding a catch-all price of `8` beneath `< 12 → 5` and `[12..64] → 10` means a 70-year-old matches only row 3. A 30-year-old matches both rows 2 and 3 (`DMN.ticketWithDefault_picks`):

- **unique and any:** the 30-year-old gets a violation.
- **collect and DWDS:** the catch-all means *"also"*. The 30-year-old gets both `10` and `8`. Adding a catch-all yellow light to the DWDS container gate turns on green, yellow, and red lights together (`DWDS.exampleB_withDefault`).
- **first:** the 30-year-old pays `10` and the 70-year-old pays `8`. Only here does the catch-all mean *"otherwise"*.

Maize proves both rules in general. A catch-all that disagrees with any reachable rule always causes a conflict (`Table.not_decisive_of_catchAll`), except under DMN's **first** policy when placed at the end of the table (`DMN.eval_first_catchAll`).

## The General Model

Both DMN and DWDS are instances of `Maize/Core.lean`. The core is built around four main types (see [Terminology](#terminology) below for how they map to DMN and DWDS):

- `Logic`: specifies what a cell can expect, what a fact can be, what an output answer looks like, when a fact matches a cell (`hit`), and which output means "no assertion" (`absent`).
- `Clause`: one rule (a row in DMN, a column in DWDS).
- `Table`: a list of clauses.
- `Is`: the observed facts, one per condition.

A clause is invoked (`Clause.Invoked`) when every cell matches its observed fact. `Table.Ought` holds when some invoked clause asserts a non-absent answer.

For any input and output, `Table.trichotomy` proves that a table gives either no answer (`Table.Silent`), one unambiguous answer (`Table.Determinate`), or conflicting answers (`Table.Deferred`).

`Table.Ought` is a **denotational semantics**: the meaning of a table is a mathematical relation. An executable evaluator (`Table.execute`) is proved to compute it (`Table.mem_execute`).

To get an automatic conflict search (`Table.findConflict`), a format only needs one small helper, a `Logic.Sampler`. It picks a single fact accepted by two cells whenever one exists (in DMN by sampling intersected shapes, and in DWDS by picking `YES` or `NO`).

### Theorems Proved for Generalised Decision Tables

- **Universal conflict search (`Table.findConflict_sound`, `Table.findConflict_none`):** if `Table.findConflict` reports an input, the table genuinely conflicts there. If it reports nothing, the output is conflict-free (`Table.Decisive`) across *all* valid inputs.
- **Conflicts always come from pairs (`Table.not_decisive_iff`, `Clause.coInvocable_iff`):** any conflict comes from two disagreeing rules that can match together. Checking whether two rules can match together breaks down independently column by column.
- **Learning more facts never creates a conflict (`Table.Deferred.of_refines`):** replacing vague facts with more precise ones (`Is.Refines`) can resolve a conflict or leave a table silent. It can never create a new conflict.
- **Reordering, repeating, and merging rules (`Table.ought_perm`, `Table.ought_cons_of_mem`, `Table.append_comm`):** before any order-dependent hit policy is applied, reordering rules, repeating an existing rule, or merging tables in any order leaves `Table.Ought` unchanged. The same holds for structure-preserving column renamings (`Table.ought_comap`) and format translations (`Table.ought_map`).

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

Maize's results fall into three tiers. No finite test suite can establish the first two:

1. **Proofs about every table and every input:** general theorems such as `Table.findConflict_sound`, `Table.findConflict_none`, `Table.Deferred.of_refines`, and `DMN.eval_unique_ne_violation`. These hold for arbitrary tables.
2. **Proofs about every input of one specific table:** universal guarantees for a concrete table. Examples include `DMN.freightFixed_never_violates` (no shipment ever causes a violation), `DMN.freight_overlap_exactly` (the two buggy freight rules collide at *only* one four-tuple), and `DWDS.container_decisive_green` (no definite facts ever make the green light ambiguous).
3. **Checked examples on specific inputs:** theorems such as `DWDS.exampleA` and `DWDS.exampleB` (Figures 30 and 31 of Potvin's thesis). These confirm that the formal definitions match published examples.

Here "every input" means every value of the types Maize models: unbounded integers, strings, and booleans in DMN, and the four states in DWDS.

## Not Covered

- **DMN:** negated tests (`not(…)`), decimals, dates and times, missing/`null` inputs, the `priority` and `output order` hit policies, `collect` aggregation (`sum`, `count`, …), and default outputs.
- **DWDS:** Maize models only the `invoked` stage of a DWDS logic gate (matching scenarios to facts). It does not model deciding which rules are `in effect` or `applicable`, multi-table pipelines, or exact-match readings of Rule 256.
- **File parsing:** neither DMN XML nor DWDS `.dwd` files are read. Tables are written directly in Lean.

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