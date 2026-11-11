# Paper coverage

[Reviewer guide](REVIEW.md) · [README](../README.md)

This statement audit covers the manuscript with SHA-256
`9c07b865c767b30dba9bb00407efa6aeafe80311934d92a62801e1b1b69a13e4`.
It includes all 26 uncommented numbered statement blocks: 20 lemmas,
the introductory and detailed versions of Theorem 1, and four corollaries.
Table 1 and the auxiliary construction and algorithm claims are included below.
The external manuscript was not modified.

The audit compares assumptions, quantifiers, sizes, starting states, rule choices
and counts. It was performed by an assistant on 10 November 2026; it is not an
independent human certification of the correspondence with the manuscript.
Lean checks the formal derivations. Authors and reviewers can inspect their
meaning through the linked definitions and statements.

## Numbered statements

Unless qualified below, declarations in this table are in
[`MainResults.lean`](../WolfeSimplex/MainResults.lean). The
[reviewer guide](REVIEW.md#paper-to-lean-map) links to individual declarations.

| Manuscript statement | Formal entry points | Alignment checked |
|---|---|---|
| Introductory Theorem 1 | `Paper.theorem1`, `Construction.certificate`, `Execution.atom_certificate` | Integer `n+1` points in dimension `m+1`, polynomial construction, correspondence from each feasible basis |
| Detailed Theorem 1(a)–(d) | `Paper.theorem1`, `PaperPath.part_a`–`part_d` | Positive common gap factor, exactly one minor cycle and the same deletion, both directions of complete-run correspondence, stopping/optimality |
| Corollary 1 | `Efficiency.corollary1_rule`, `Efficiency.MachineAlgorithm.certificate` | History-dependent rules; polynomial and strongly polynomial implications, including the executed wrapper |
| Corollary 2 | `PaperCorollary2` family theorems listed below | Five exponential and two expected superpolynomial bounds; shortest-atom initialization for linopt and minnorm |
| Corollary 3 | `nnls` | Integer `(n+3) × (2n+2)` matrix, every complete Lawson–Hanson execution has exactly `2^n+n+1` insertions |
| Corollary 4 | `PaperCorollary4.corollary4_queries`, `corollary4_count_extended` | Conditional polynomial answer/count reductions from the cited native source problems, including infinite-capacity normalization |
| Lemma 1 | `affine_min` | Parts (a)–(c), including affine-minimizer and optimality criteria; a support with an affine minimizer is nonempty |
| Lemma 2 | `hom` | Admissibility of the induced LP, feasible bases in both directions, solution/dual/reduced-cost formulas and pivots/runs |
| Lemma 3 | `direction` | Both atom and gap identities |
| Lemma 4 | `corral` | Affine independence, projection/coefficient identities, gap formula and positive scale |
| Lemma 5 | `bases_corrals` | Lower bounds, direction bounds, coefficient error and strict positivity |
| Lemma 6 | `pivot` | Exactly one minor cycle, deletion and next support |
| Lemma 7 | `identities` | Basic solution and direction uniqueness, objective and dual identities |
| Lemma 8 | `T_bound` | Strict bound for every feasible point, not only vertices |
| Lemma 9 | `induced_facts` | All three induced-LP identities |
| Lemma 10 | `encoding`, construction/execution certificates | Integrality, coefficient and binary-length bounds; executed polynomial construction |
| Lemma 11 | Rule transfers, family theorems and Table 1 entries below | All six rows, actual Wolfe runs, exact random prefix laws and expected counts |
| Lemma 12 | `shield_lp` | Admissibility, polynomial data size, basis correspondence, reduced costs and leaving label |
| Lemma 13 | `init_a`, `init_b`, `init_c` | Partial-start corrals, exact gaps, no minor cycles and unique shortest atom |
| Lemma 14 | `init_linopt`, `init_leastLabel`, `Execution.shield_certificate` | Initialization prefix, subsequent Dantzig/Bland run, order restriction and polynomial preparation |
| Lemma 15 | `km_admissible`, `km_dantzig`, `km_bland` | Actual Klee–Minty LP, both exact `2^n−1` counts, unique Dantzig choices |
| Lemma 16 | `weighted_a`, `weighted_b`, `weighted_c` | Admissibility and size, basis/pivot correspondence, initial corrals and strict norm order |
| Lemma 17 | `minnorm`, `Execution.weighted_certificate` | Distinct norms, unique shortest start, full initialization prefix, Bland run and polynomial preparation |
| Lemma 18 | `km_linopt`, `km_minnorm` | Integer `2n+2` points, dimension `n+2`, polynomial encoding, shortest start and exact `2^n+n+1` corrals for every tie resolution |
| Lemma 19 | `nnls_ls` | Independent columns, unique least-squares solution and residual/gap formula |
| Lemma 20 | `lh_wolfe_major`, `lh_wolfe` | Matched choices and deletions under the stated single-zero condition; Corollary 3 proves that condition internally |

## Corollary 2 and Table 1

The table's `n` counts **source LP variables**. The cap adds one LP variable;
the atom construction adds one more point. Thus the cited-family transfers use
`n+2` points. The internally proved Klee–Minty family has `2d` source variables.

| Claim | Checked entry points in `PaperCorollary2` |
|---|---|
| Linopt: `Ω(2^(n/2))` | `linopt_table1`, from `km_linopt`; `2^d ≤ f` insertions from the unique shortest atom |
| Least-index: `Ω(2^(n/2))` | `least_index_table1`; `2^d ≤ 2f` on the actual Klee–Minty Wolfe runs, `d ≥ 1` |
| Least-inserted: `2^Ω(n)` | `zadeh_family`, exact history/run transport and `exponential_add_two` |
| Round-robin: `2^Ω(n)` | `cunningham_family`, including the initial index and cyclic order |
| Random: `2^tildeΩ(n^(1/4))` | `random_edge_table1`; concrete polynomial construction: `random_edge_table1_mdp` |
| Random-order: `2^tildeΩ(sqrt n)` | `random_bland_table1`; concrete polynomial construction: `random_bland_table1_mdp` |
| Minnorm and shortest-start conclusions | `shortest_start_growth`, from internally proved `km_linopt` and `km_minnorm` |
| Qualitative expected superpolynomial conclusions | `random_edge_family`, `random_bland_family` |

The quantitative statements are in [Table1](../WolfeSimplex/Proofs/Table1.lean),
[RandomRates](../WolfeSimplex/Proofs/RandomRates.lean) and
[RandomSource](../WolfeSimplex/Proofs/RandomSource.lean).
`StretchedExponentialBound p` explicitly means an eventual lower bound
`2^(a (N+1)^p / log(N+2)^k)`, up to a positive multiplicative constant,
with `a > 0` and a fixed natural `k`. Adding two points changes the constant
to `a/3` and preserves `p = 1/4` or `p = 1/2` exactly.

Random-Edge samples a fresh uniform improving label. Random-Bland samples one
uniform permutation for the entire run, as required for random-order.
The Random-Facet process is not used. Expected total counts are defined by
monotone truncation and may be infinite; equality is proved at every finite
prefix before taking expected lengths.

`MDPSource` accepts rational source data, positive supplies, the column-owner
sign pattern, a feasible initial basis and an attained optimum. Lean derives
rank and nondegeneracy, executes denominator clearing, constructs the cap and
integer atoms, and executes the starting-support mask. It proves exact
expectations, measured polynomial bit work and polynomial target encoding length.
The source family supplies its published lower bound and polynomial encoding
size; no Wolfe lower bound or target construction cost is a premise.

## Additional claims and conventions

- Section 2.2: `wolfe_well_defined` proves progress, termination, strict norm
  decrease and at most `D` minor cycles per major cycle.
- Appendix C: cap/scaling and all deterministic, history and random-rule
  correspondences are listed in the reviewer guide. Adding fixed labels
  preserves history counts and cyclic order; permutation restriction gives
  the correct uniform random order.
- Appendix C.4: `RunLocal` needs nondegeneracy only on visited bases.
  `NetworkIncidence` proves row deletion and native forest/basis identities.
  `NetworkFlow` proves capacity-slack conversion, including upper-bound signs
  and bound flips. `NetworkPreparation` certifies executed native conversion
  and initial-mask preparation; no source-run simulation is used to construct
  the target.
- `InfiniteCapacity` models absent upper bounds in the original network ratio
  test and proves conservation-based finite replacement. The extended source
  interface derives its finite normalized run internally. Executed capacity
  arrays, polynomial binary size and measured normalization cost are composed
  in `corollary4_count_extended`; a finite-capacity variant of DS18's hardness
  result is not a separate source premise.
- A run of length `f` has `f` pivots/insertions and `f+1` bases/corrals.
  Lawson–Hanson starts from the empty active set, so its first insertion
  accounts for the extra one in Corollary 3.
- Lower bounds with a suitable corral start do not claim a singleton start.
  Shortest-point starts are proved separately where the paper claims them.
  Complete and partial runs, and existence versus all tie resolutions, are
  distinguished in the formal statements.
- The introductory Theorem 1 is read under the paper's standing admissibility
  assumptions, including rational data scaled to integers and full row rank.
  Zero-based Lean labels and squared norms do not change the mathematical
  statements.

## External premises and verification boundary

The scope is the paper's new deductions **assuming the cited previous work**.
External source-family results are ordinary theorem hypotheses, not axioms:

| Prior work | Source facts assumed |
|---|---|
| DFH23 / AF17 | Rational Zadeh/Cunningham families, their initial states and exponential source runs |
| FHZ11/Han12 | Rational Random-Edge family, its structural/encoding facts and fourth-root expected lower bound |
| FHZ14 | Rational one-permutation Random-Bland family, structural/encoding facts and square-root expected lower bound |
| FS15 | Rational MDP data, feasible start, structural promises, robust queried-variable answer and polynomial source encoding |
| DS18 | Native rational network data and absent upper bounds, one-way source/sink endpoint structure for those arcs, initial tree/bound state, positive finite capacities, balanced row deletion, interior tree flows and unique entering choices along the hard run, source count and polynomial source encoding |

The primary randomized results are the authors'
[Random-Edge paper](https://oliverfriedmann.com/downloads/papers/random_edge_lower_bound.pdf)
and [Random-Bland paper](https://arxiv.org/abs/1410.7530).
The exact FS15/DS18 interfaces and links are in the
[Corollary 4 review](REVIEW.md#corollary-4-checked-reductions-and-executed-preprocessing).
The internal Klee–Minty, shortest-start and NNLS proofs do not require a cited
lower-bound theorem as a hypothesis.

Time claims use the documented arithmetic/array interpreter with charged data,
allocation, indexed access and control, and a quadratic maximum-word-width bit
charge. They do not certify Lean's compiler/runtime or a binary Turing-machine
implementation. NP and PSPACE are not defined internally: Corollary 4 proves
polynomial reductions and exact answers/counts from FS15/DS18's source problems.
Their complexity-class hardness is the accepted literature premise.

`scripts/check.sh` checks the integrated library, all imported project axiom
dependencies, selected proof-term dependencies, the three-module Theorem 1
statement boundary and executable regressions. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed. No new paper conclusion is
assumed as a literature premise.

The full twelve-check suite passed on 10 November 2026 with all new modules in
the default imports. All five external manuscript sources matched the archive.

The subsequent submission review found that infinite-to-finite capacity
normalization had been implicit at the DS18 source interface. The formalization
now derives it from the original absent-bound network semantics and its endpoint
structure, with exact counts and executed polynomial preprocessing. The dedicated
regression includes an uncapacitated entering arc with a zero dummy capacity,
rational supplies/capacities and a nonterminal circulation for which arbitrary
finite capping would be invalid.
The expanded thirteen-check integrated suite passed with all normalization
modules in the default imports, including the project axiom and dependency audits.
