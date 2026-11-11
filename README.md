# WolfeSimplex

Lean 4 formalization accompanying **Wolfe's Minimum-Norm-Point Method Generalizes
the Simplex Method** ([arXiv:2611.12680](https://arxiv.org/abs/2611.12680)).

Authors: Yann Disser and Nils Mosis (TU Darmstadt, Germany).
To cite this formalization, see [`CITATION.cff`](CITATION.cff).
Version v1.0 (the version accompanying the arXiv paper) is archived on Zenodo:
[doi:10.5281/zenodo.24136107](https://doi.org/10.5281/zenodo.24136107).

## Verification status

**Theorem 1, Corollaries 1–4, and all numbered statements leading up to them
have checked Lean proofs**, assuming the correctness of the cited results from
previous work. This includes the bounds in Table 1.

Running-time claims use the documented arithmetic/array model.

The check suite validates the current formal statements and their axiom dependencies. The
[reviewer guide](docs/REVIEW.md) explains the assumptions and proof references;
the [coverage record](docs/COVERAGE.md) maps every paper result.

## Start here

1. Read [`Paper.theorem1`](WolfeSimplex/PaperTheorem1.lean) with the three core
   definitions: [Simplex](WolfeSimplex/Defs/Simplex.lean),
   [Wolfe](WolfeSimplex/Defs/Wolfe.lean) and
   [Induced](WolfeSimplex/Defs/Induced.lean).
2. Follow [`PaperPath`](WolfeSimplex/Proofs/PaperPath.lean) for the composition
   through the paper's numbered lemmas.
3. For construction resources, read
   [`Construction.certificate`](WolfeSimplex/Construction/Budget.lean).
   The [primitive execution certificates](WolfeSimplex/Execution/Budget.lean)
   cover this construction and both shortest-vector preparations.
   Corollary 1 has [iteration](WolfeSimplex/Efficiency/RuleIterations.lean) and
   [execution-cost](WolfeSimplex/Efficiency/MachineTransfer.lean) entry points.
   For additional results, use the
   [paper-to-Lean map](docs/REVIEW.md#paper-to-lean-map).

Lean checks the proofs. Reviewers still need to interpret the definitions and
statements against the paper; the [guide](docs/REVIEW.md#review-boundary) explains
this boundary.

## Reproduce the checks

Install [elan](https://github.com/leanprover/elan), download and unpack the
code, then run in its top-level folder:

```sh
lake exe cache get
sh scripts/check.sh
```

[Lean](lean-toolchain) and [Mathlib dependencies](lake-manifest.json) are pinned.
The initial dependency/cache download requires network access.

The check command builds the library, rejects unexpected axioms across all
imported project declarations, checks the selected paper-proof dependencies and
the three-module statement boundary, and evaluates construction, trace-projection,
primitive-execution, run-local and capacity-slack/bound-flip examples.
It also checks native incidence/forest, Corollary 4 rational count/query examples,
and the quantitative Table 1 rates and rational source construction.
Infinite-capacity normalization is checked against native network pivots and counts.
It stops on failure and displays the failed command's log. Run the individual
[scripts](docs/REVIEW.md#checks) to see their full output, including build warnings.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted axiom dependencies.
