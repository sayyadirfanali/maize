# Open Questions on DWDS

Questions that came up while formalising the [DWDS](https://gitlab.com/xalgorithms-alliance/data-with-direction-specification/dwds-documents/-/tree/master/current) (Potvin, 2023 DBA thesis) in `Maize/DWDS.lean` against the general table model in `Maize/Core.lean`.

## 1. `YES-AND-NO` against `YES-OR-NO` in `DWDS.hit`

In §5.5.3 of the thesis, the hit relation matches any two states except `YES` against `NO` and `NO` against `YES`, but the exact behaviour of `YES-AND-NO` (`10`) against `YES-OR-NO` (`11`) is not explicitly stated.

- In `Maize/DWDS.lean`, `DWDS.hit` currently treats `YES-AND-NO` against `YES-OR-NO` as a hit (marked provisional).
- Should `YES-AND-NO` hit `YES-OR-NO` in both directions, in one direction only, or miss?

## 2. `NOT` (`00`) as silence (`Logic.absent`) vs. an explicit mode

In `Maize/DWDS.lean`, `DWDS.Mode.not` (`00`) is modelled as `Logic.absent`, meaning a scenario with `NOT` on an assertion row makes no claim about that assertion—and therefore never causes a `Table.Deferred` conflict when another invoked scenario asserts `MUST`, `MAY`, or `SHOULD`.

- Does `NOT` in DWDS always mean "this scenario makes no assertion here", or can `NOT` conflict with another non-`NOT` mode (such as `MUST` or `SHOULD`) when two scenarios match?

## 3. Catch-all `YES-OR-NO` scenarios ("otherwise" vs. "also")

A scenario with `YES-OR-NO` in every input condition (`DWDS.universal_yesOrNo`) matches every input (`Clause.invoked_of_universal`). Authors often write a trailing catch-all scenario intending a fallback ("otherwise"), but in DWDS all matching scenarios contribute their modes (`exampleB_withDefault`).

- In DWDS practice, are catch-all scenarios intended to act as unconditional contributors ("also"), or is there an override/precedence rule—or a higher-level stage outside `invoked`—that makes them behave as a fallback ("otherwise")?

## 4. Independent per-assertion decisions and simultaneous conflicting signals

In `Maize/Core.lean`, `Table.Ought`, `Table.Determinate`, and `Table.Deferred` are defined **per assertion** (`a : Assertion`). In the Figure 28 container table (`DWDS.container`), under the Figure 31 input (`isB`: loaded, not inspected, locked), both the green light and the red light are individually `Table.Determinate` with `MUST` at the same time (`DWDS.exampleB_green_and_red`), while `stevedore` and `insurance` are `Table.Deferred`.

- Is per-assertion independence the intended semantics of a DWDS logic gate, or are multi-assertion combinations (such as `MUST` on both green and red lights) intended to be checked or resolved jointly?

## 5. How "Rule 256" relates to `DWDS.hit` and scenario invocation

The thesis refers to "Rule 256" in connection with four-state matching and rule evaluation.

- How does Rule 256 relate to `DWDS.hit` and `Clause.Invoked`—is it a distinct matching/filtering rule, a way of interpreting four-state combinations, or a rule governing later stages of a logic gate?

## 6. Scope beyond `invoked`

`Maize/DWDS.lean` models the `invoked` relation between scenarios and observed facts, and checks whether invoked scenarios agree or defer on each assertion.

- Which parts of the broader DWDS pipeline (such as `in effect`, `applicable`, cross-table composition, or deferral resolution) are most important to model next if we extend this semantics?
