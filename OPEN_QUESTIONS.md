# Open Questions on DWDS

Questions that came up while formalising the [DWDS](https://gitlab.com/xalgorithms-alliance/data-with-direction-specification/dwds-documents/-/tree/master/current) logic gates (Potvin, 2023 DBA thesis) in `Maize/DWDS.lean` against the general table model in `Maize/Core.lean`.

## 1. `YES-AND-NO` against `YES-OR-NO` in `DWDS.hit`

In §5.5.3 of the thesis, the hit relation matches any two states except `YES` against `NO` and `NO` against `YES`, but the exact behaviour of `YES-AND-NO` (`10`) against `YES-OR-NO` (`11`) is not explicitly stated.

- In `Maize/DWDS.lean`, `DWDS.hit` currently treats `YES-AND-NO` against `YES-OR-NO` as a hit (marked provisional).
- Should `YES-AND-NO` hit `YES-OR-NO` in both directions, in one direction only, or miss?

## 2. `NOT` (`00`) as silence (`Logic.absent`) vs. an explicit mode

In `Maize/DWDS.lean`, `DWDS.Mode.not` (`00`) is modelled as `Logic.absent`, meaning a scenario with `NOT` on an assertion row makes no claim about that assertion—and therefore never causes a `Table.Deferred` conflict when another invoked scenario asserts `MUST`, `MAY`, or `SHOULD`.

- Does `NOT` in DWDS always mean "this scenario makes no assertion here", or can `NOT` conflict with another non-`NOT` mode (such as `MUST` or `SHOULD`) when two scenarios match?

## 3. Catch-all `YES-OR-NO` scenarios ("otherwise" vs. "also")

A scenario with `YES-OR-NO` in every input condition (`DWDS.universal_yesOrNo`) matches every input (`Clause.invoked_of_universal`). A rule author might add a trailing catch-all scenario intending a fallback ("otherwise"), but in DWDS all matching scenarios contribute their modes (`DWDS.exampleB_withDefault`).

- In DWDS practice, are catch-all scenarios intended to act as unconditional contributors ("also"), or is there an override/precedence rule—or a higher-level stage outside `invoked`—that makes them behave as a fallback ("otherwise")?

## 4. Does Rule 256 assume exact matching?

Rule 256 (§5.4.4) contains all 256 permutations of four input states, with output rows identical to the input rows, and sifting is expected to return output identical to the input. That holds if exactly one scenario is invoked.

Under `DWDS.hit`, though, a definite fact is hit by three of the four expected states (`YES` by `01`, `10` and `11`; `NO` by `00`, `10` and `11`). So for four definite facts, 3⁴ = 81 of the 256 scenarios are invoked at once, and every assertion receives several different modes. The output only equals the input if matching is exact (each state hits only itself).

- Is Rule 256 evaluated with exact matching rather than the hit relation? If so, where in the sieve does that difference apply?

## 5. Scope beyond `invoked`

`Maize/DWDS.lean` models the `invoked` relation between scenarios and observed facts, and checks whether invoked scenarios agree or defer on each assertion.

- Which parts of the broader DWDS pipeline (such as `in effect`, `applicable`, cross-table composition, or deferral resolution) would you consider most important?
