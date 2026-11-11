# Reviewer guide

[Back to README](../README.md). Paper numbers below refer to the manuscript
identified in the [alignment record](#alignment-record).

## Current coverage status

All numbered results and Table 1's quantitative bounds have formal proofs under
the literature premises and computation model below. The
[coverage record](COVERAGE.md) maps every statement and records its assumptions,
sizes, starting states, counts and source interfaces. Corollary 4 includes
executed native network preprocessing, with measured cost rather than an
assigned polynomial charge. The source lower-bound/hardness results remain
explicit literature premises.

## Review boundary

For the main correspondence, review
[`Paper.theorem1`](../WolfeSimplex/PaperTheorem1.lean) and the project definitions
in [Simplex](../WolfeSimplex/Defs/Simplex.lean),
[Wolfe](../WolfeSimplex/Defs/Wolfe.lean) and
[Induced](../WolfeSimplex/Defs/Induced.lean). These three files contain 155 nonblank
lines excluding comments. The statement gives integral coordinates and signed
binary lengths, then Theorem 1(a)–(d). Construction resources are a separate
[certificate](../WolfeSimplex/Construction/Budget.lean).

Lean checks derivations from the definitions and stated hypotheses. Matching
those definitions and statements to the manuscript remains a human review task.
They are not additional axioms. The axiom audit permits only `propext`,
`Classical.choice` and `Quot.sound`, and rejects `sorryAx` and any extra axiom.

[`PaperPath`](../WolfeSimplex/Proofs/PaperPath.lean) follows this composition:

| Paper step | Dependencies checked in the proof term |
|---|---|
| Lemma 4, gap formula | Lemma 3's direction identity |
| Theorem 1(a) | Lemmas 2, 4 and 5 |
| Theorem 1(b) | Lemmas 2 and 6 |
| Theorem 1(c) | Parts (a) and (b), by induction |
| Theorem 1(d) | Part (a) and Lemma 1(c) |
| Integral coordinates and binary length | Lemma 10's estimates and the `Nat.size` bound |
| Corollary 1 | Theorem 1(c), history-run transport, primitive constructor output and polynomial input growth |
| Preparation costs | Correct shield/weighted output, intermediate bounds, addresses and polynomial bit work |
| Corollary 2 | Integerization, cap/rule transport, expected-count equality and growth after adding two labels |

The path check enforces selected direct dependencies and the three-module
statement boundary. Dependency presence is what is checked: additional auxiliary
arguments are permitted. The audit does not certify identical prose, line-by-line
translation or uniqueness of the proof route.

## Paper-to-Lean map

The 55 public statements below are in
[MainResults.lean](../WolfeSimplex/MainResults.lean). Links jump to their declarations;
proof implementations are in `WolfeSimplex/Proofs/`. Each result is subject to its
explicit hypotheses and the qualifications following this table.

| Paper result | Lean declarations | Checked content |
|---|---|---|
| Lemma 1 | [affine_min](../WolfeSimplex/MainResults.lean#L59) | Affine-minimizer criteria, existence and uniqueness |
| Section 2.2 | [wolfe_well_defined](../WolfeSimplex/MainResults.lean#L80) | Progress, termination, strict norm decrease; at most `D` minor cycles per major cycle |
| Theorem 1 | [equivalence_integral](../WolfeSimplex/MainResults.lean#L99), [equivalence_size](../WolfeSimplex/MainResults.lean#L108), [equivalence_a](../WolfeSimplex/MainResults.lean#L116), [equivalence_b](../WolfeSimplex/MainResults.lean#L136), [equivalence_c](../WolfeSimplex/MainResults.lean#L151), [equivalence_d](../WolfeSimplex/MainResults.lean#L162) | Integral bounded atoms and correspondence (a)–(d); combined entry point: `Paper.theorem1` |
| Lemma 2 | [hom](../WolfeSimplex/MainResults.lean#L217) | Homogenization, bases, reduced costs, leaving labels, pivots and runs |
| Lemma 3 | [direction](../WolfeSimplex/MainResults.lean#L242) | Atom and gap identities |
| Lemma 4 | [corral](../WolfeSimplex/MainResults.lean#L254) | Projection and gap/reduced-cost formulas |
| Lemma 5 | [bases_corrals](../WolfeSimplex/MainResults.lean#L270) | Coordinate/direction bounds and corral property |
| Lemma 6 | [pivot](../WolfeSimplex/MainResults.lean#L285) | One minor cycle, the deletion and next corral |
| Lemma 7 | [identities](../WolfeSimplex/MainResults.lean#L45) | Basic solution, dual and direction identities |
| Lemma 8 | [T_bound](../WolfeSimplex/MainResults.lean#L176) | Strict feasible coordinate-sum bound |
| Lemma 9 | [induced_facts](../WolfeSimplex/MainResults.lean#L184) | All three induced-LP identities |
| Lemma 10 | [encoding](../WolfeSimplex/MainResults.lean#L199) | Integrality and magnitude estimates; resource certificate below |
| Lemma 11 / Corollary 2: deterministic rules | [rules_dantzig](../WolfeSimplex/MainResults.lean#L311), [rules_bland](../WolfeSimplex/MainResults.lean#L323) | Dantzig/linopt and Bland/least-index run correspondences |
| Lemma 11 / Corollary 2: history rules | [rules_zadeh](../WolfeSimplex/MainResults.lean#L334), [rules_cunningham](../WolfeSimplex/MainResults.lean#L345), [rules_cunningham_slack](../WolfeSimplex/MainResults.lean#L359), [rules_unique_steps](../WolfeSimplex/MainResults.lean#L372) | Zadeh/least-inserted, Cunningham/round-robin and unique-step correspondences |
| Lemma 11 / Corollary 2: random rules | [rules_random_edge](../WolfeSimplex/MainResults.lean#L383), [rules_random_bland](../WolfeSimplex/MainResults.lean#L393) | Equality of finite-prefix distributions |
| Appendix C.2: cap | [cap_admissible](../WolfeSimplex/MainResults.lean#L407), [cap_bases](../WolfeSimplex/MainResults.lean#L418), [cap_unique_steps](../WolfeSimplex/MainResults.lean#L433), [cap_zadeh](../WolfeSimplex/MainResults.lean#L446), [cap_cunningham](../WolfeSimplex/MainResults.lean#L457), [cap_random_edge](../WolfeSimplex/MainResults.lean#L471), [cap_random_bland](../WolfeSimplex/MainResults.lean#L481) | Admissibility, bases and rule transfers from cap-augmented starts |
| Section 3: integrality | [scale_bases](../WolfeSimplex/MainResults.lean#L500), [scale_runs](../WolfeSimplex/MainResults.lean#L512), [scale_random_runs](../WolfeSimplex/MainResults.lean#L528), [scale_integral](../WolfeSimplex/MainResults.lean#L538) | Positive scaling, preserved runs and rational-to-integer data |
| Lemma 12 | [shield_lp](../WolfeSimplex/MainResults.lean#L565) | Shield admissibility, size and simplex data |
| Lemma 13 | [init_a](../WolfeSimplex/MainResults.lean#L581), [init_b](../WolfeSimplex/MainResults.lean#L592), [init_c](../WolfeSimplex/MainResults.lean#L608) | Initial cycles and unique shortest atom |
| Lemma 14 | [init_linopt](../WolfeSimplex/MainResults.lean#L623), [init_leastLabel](../WolfeSimplex/MainResults.lean#L647) | Linopt/least-index initialization and Dantzig/Bland runs; size bound |
| Lemma 15 | [km_admissible](../WolfeSimplex/MainResults.lean#L742), [km_dantzig](../WolfeSimplex/MainResults.lean#L750), [km_bland](../WolfeSimplex/MainResults.lean#L763) | Klee–Minty admissibility and exactly `2^n − 1` pivots |
| Lemma 16 | [weighted_a](../WolfeSimplex/MainResults.lean#L670), [weighted_b](../WolfeSimplex/MainResults.lean#L687), [weighted_c](../WolfeSimplex/MainResults.lean#L701) | Weighted shield, size, initial cycles and strict norm order |
| Lemma 17 | [minnorm](../WolfeSimplex/MainResults.lean#L716) | Minnorm initialization, distinct norms, bounded integer atoms and Bland runs |
| Lemma 18 | [km_linopt](../WolfeSimplex/MainResults.lean#L780), [km_minnorm](../WolfeSimplex/MainResults.lean#L792) | `2n + 2` atoms in dimension `n + 2`; exactly `2^n + n + 1` corrals |
| Lemma 19 | [nnls_ls](../WolfeSimplex/MainResults.lean#L812) | Unique least-squares vector and residual/gap formula |
| Lemma 20 | [lh_wolfe_major](../WolfeSimplex/MainResults.lean#L830), [lh_wolfe](../WolfeSimplex/MainResults.lean#L860) | Lawson–Hanson/Wolfe correspondence under a single-zero condition |
| Corollary 3 | [nnls](../WolfeSimplex/MainResults.lean#L889) | Integer `(n + 3) × (2n + 2)` matrix; exactly `2^n + n + 1` insertions for every complete execution; partial-length bound |

The Klee–Minty, shortest-atom and NNLS lower-bound examples are proved internally.
The four cited simplex lower-bound families are explicit premises of the complete
[family transfers](#corollary-2-and-literature-premises) below.

## Assumptions and conventions

- **Admissibility:** integer `A, b, c`; `m ≥ 1`; full row rank; a nonempty bounded
  feasible set; every feasible basis nondegenerate. See `IntLP.IsAdmissible`.
- **Labels and coordinates:** Lean labels start at zero. `Fin.castSucc` embeds an
  original label; `Fin.last` is the added label. Atom coordinate zero is the cost
  coordinate; the induced LP places its normalization row last. Norms are squared.
- **Counts and stopping:** complete runs include the terminal condition. Length
  `f` means `f` pivots/insertions and `f + 1` bases/corrals. The NNLS lower bound
  includes its first insertion from the empty active set.
- **Ties:** deterministic choices allow every tied minimizer. Rank functions may
  have ties; injective ranks give a total order. The minnorm construction uses a permutation.
- **Randomness:** Random-Edge draws a fresh uniform improving label each step;
  Random-Bland draws one uniform permutation initially. Expected total count is
  the supremum of expected truncated counts, allowing infinity.
- **Lawson–Hanson:** Wolfe deletes one zero coefficient per minor cycle;
  Lawson–Hanson deletes all zeros per inner iteration. Lemma 20 assumes a unique
  zero at each relevant step. Corollary 3 discharges this condition internally.
- **Cap:** attained optimum and nondegenerate feasible bases are hypotheses.
  Transfer starts at the corresponding cap-augmented basis; survival of every
  originally feasible point is not asserted.

## Efficiency transfer (Corollary 1)

There are two public formulations:

- [`corollary1_rule`](../WolfeSimplex/Efficiency/RuleIterations.lean) matches
  the paper's major-cycle argument. Every polynomial bound on partial Wolfe
  runs gives a polynomial pivot bound, in binary input size or dimensions alone.
  Rules may depend on the complete inserted-label history. `inducedRule_total`
  proves that an insertion rule able to select an improvement induces a pivot
  rule with that property.
- [`MachineAlgorithm.corollary1`](../WolfeSimplex/Efficiency/MachineTransfer.lean)
  transfers the running-time guarantees of a complete Wolfe program. Review its
  [machine semantics](../WolfeSimplex/Execution/Machine.lean) and
  [adapter](../WolfeSimplex/Efficiency/Machine.lean). One fixed program operates on
  explicit input arrays, with arithmetic, indexed memory, branches, loops and
  emitted supports. Work and numeric widths come from the unique halting
  execution. Termination, correctness and uniform polynomial bounds for that
  supplied program are hypotheses; no efficient Wolfe program is asserted.

`reduction_input_executed` proves that the point-array frame passed to the machine
is exactly the first-order constructor's output. `MachineAlgorithm.certificate` bundles this agreement with actual halting
executions and both time implications. The induced procedure charges
that constructor, the complete Wolfe execution, start-mask preparation, trace
projection and output. The [entering-label scan](../WolfeSimplex/Efficiency/PivotPlan.lean)
gives the corresponding pivot plan. No second linear-system solve is needed.

[Report summaries](../WolfeSimplex/Efficiency/Procedure.lean) and the
[polynomial closure lemmas](../WolfeSimplex/Efficiency/Corollary1.lean) are internal
interfaces. A raw report's cost fields alone do not certify an execution; the
public machine adapter derives those fields from its interpreter. Ordinary
polynomiality bounds work and width by binary input length. Strong polynomiality
bounds work by dimensions alone and width by binary input length. The uniform
quadratic bit charge also gives polynomial bit work for the complete wrapper.

## Construction resources

[`Construction.certificate`](../WolfeSimplex/Construction/Budget.lean) proves, for
integer input with `m ≥ 1`, coordinatewise equality of the executable integer
output with `IntLP.atom`, exactly `7mn + 9m + 6n + 20` arithmetic operations,
peak magnitude at most `N²K`, and bit budget at most `54760 · (3I)⁸`.
[`run_width_le`](../WolfeSimplex/Construction/Budget.lean) bounds signed width by
`1 + 36(m + 1)² · Nat.size ((m + 1)W)`.

To review these claims, read the certificate with
[Build](../WolfeSimplex/Construction/Build.lean),
[Cost](../WolfeSimplex/Construction/Cost.lean) and
[Encoding](../WolfeSimplex/Construction/Encoding.lean). `I` is the length of an
explicit dense binary encoding of both dimensions and all input entries, using
sign bits and unary length prefixes. Correctness needs no admissibility assumption
and the executable construction performs no LP solve or admissibility test.

The model charges addition, subtraction, multiplication, absolute value and
comparison at the square of the run’s maximum signed operand/result width.
Powers use
repeated multiplication. This original `bitBudget` counts arithmetic only. The
new [Work certificate](../WolfeSimplex/Construction/Work.lean) additionally proves
`35mn + 41m + 40n + 105` total arithmetic/control/cell charges, bounded by
`150(m+n+1)²`, and polynomial widths including control counters. `fullWidth` is
a conservative bound. These additional charges cover the vector schedule's allocation,
indexing and loop control. The public machine transfer instead charges the
first-order interpreter's constructor work.
[`Execution.atom_certificate`](../WolfeSimplex/Execution/Budget.lean) proves its
exact output, dimension-only work, full word width and polynomial bit work;
`reduction_input_executed` identifies the common point-array frame. Resource-monitor execution,
binary arithmetic implementations, Lean's compiler and compiled runtime are
outside this model. The polynomials are loose bounds.

## Shortest-vector preparation resources

[`Execution.shield_certificate` and `weighted_certificate`](../WolfeSimplex/Execution/Budget.lean)
complete the time clauses for Lemmas 14 and 17. For any integer input with
`m ≥ 1`, basis enumeration and (for the weighted case) permutation, they prove:

- Execution produces exactly the shield/weighted-shield integer atoms.
- Arithmetic/control/cell work is at most `1,100,000,000 (m+n+2)^12`.
- Signed width, including numeric data, literal addresses and counters, is at
  most `2,000,000,000 (sizeParameter+1)^13`.
- Bit work is at most `10^50 (1+I)^38`, for the explicit binary input length `I`.

These deliberately loose polynomials establish complexity classes. The mathematical
starting behavior and output-size bounds remain the statements in `MainResults`.
The first-order [interpreter](../WolfeSimplex/Execution/Code.lean) has no arbitrary
numeric-function primitive or caller-supplied cost fields. Coefficients are input
cells. [Cached determinant code](../WolfeSimplex/Execution/Bird.lean),
[canonicalization](../WolfeSimplex/Execution/Canonical.lean) and
[shield programs](../WolfeSimplex/Execution/Shield.lean) implement the preparation.
The determinant recurrence and its numeric growth are checked, so determinant
and adjugate calculation are included in the bounds.

Inputs are explicit dense integer arrays and finite tables of labels. The model
uses indexed integer arrays and primitive integer arithmetic, with a
quadratic charge on the maximum word width. Copying, allocation and control are
charged. Resource-monitor evaluation, binary arithmetic implementations, and
Lean's compiler/runtime are outside the model.

## Corollary 2 and literature premises

The seven lower bounds have the following entry points:

| Wolfe rule | Formal result | Source |
|---|---|---|
| Linopt | `km_linopt`, `shortest_start_growth` | Internal Klee–Minty proof; shortest-point start |
| Minnorm | `km_minnorm`, `shortest_start_growth` | Internal proof; shortest-point start and distinct norms |
| Least-index | `least_index`, `least_index_growth` | Internal Klee–Minty/Bland proof |
| Least-inserted | `zadeh_family` | Cited Zadeh family (DFH23) |
| Round-robin | `cunningham_family` | Cited Cunningham family (AF17) |
| Random | `random_edge_family`, `random_edge_table1_mdp` | Cited Random-Edge family (FHZ11/Han12) |
| Random-order | `random_bland_family`, `random_bland_table1_mdp` | Cited Random-Bland family (FHZ14) |

The internal assembly is in [Corollary2Internal](../WolfeSimplex/Proofs/Corollary2Internal.lean);
the four independent cited-family transfers are in
[Corollary2Families](../WolfeSimplex/Proofs/Corollary2Families.lean). They accept
[RationalInput](../WolfeSimplex/Proofs/Corollary2Scaling.lean): rational coefficients,
`m ≥ 1`, an attained optimum, nondegenerate feasible bases and a specified
feasible starting basis. Rank follows from that basis. Each family supplies its
own source run/expected bound and an unbounded number of labels.

Lean proves integerization with preserved deterministic histories and random
prefix laws, the cap's admissibility and start, integral target points, and the
rule transfers. Deterministic bounds transfer a witnessed run, preserving its
tie-breaking history; they do not require every source tie-break to be slow.
Expected counts are preserved exactly. The
[growth lemmas](../WolfeSimplex/Proofs/Corollary2Growth.lean) prove that adding two
labels preserves the exponential and superpolynomial bounds. These cited source
facts are theorem arguments, not extra axioms.

[Table1](../WolfeSimplex/Proofs/Table1.lean) exposes the deterministic
`Ω(2^(n/2))` inequalities. [RandomRates](../WolfeSimplex/Proofs/RandomRates.lean)
proves that adding two points preserves the precise fourth-root and square-root
exponents with any fixed logarithmic loss. Its Table 1 theorems preserve expected
counts exactly. [RandomSource](../WolfeSimplex/Proofs/RandomSource.lean) gives
concrete rational MDP interfaces: nondegeneracy follows internally from the
positive supplies/column-owner sign pattern; rank follows from the initial
basis. It proves executed integerization, cap/atom output and initial support,
polynomial measured construction cost and polynomial output encoding length.
The cited family's source encoding bound and source expected lower bound are
the external quantitative premises. See the [coverage record](COVERAGE.md#corollary-2-and-table-1)
for the size convention and explicit asymptotic definition.

[BoundTransfers](../WolfeSimplex/Proofs/BoundTransfers.lean) additionally provides
generic iteration-property, choice-totality, count/expectation and queried-label
transfers. Corollary 4's conditional transfer and budget theorems are in
[`Corollary4.lean`](../WolfeSimplex/Proofs/Corollary4.lean), with the precise
external-source and computation-model boundary described below.

## Nondegeneracy along a run (Appendix C.4)

[`RunLocal.lean`](../WolfeSimplex/Proofs/RunLocal.lean) supplies the weaker
correspondence needed by the counting argument: only the bases visited by the
source run must be nondegenerate. The LP may have degenerate feasible bases
elsewhere. The original globally admissible theorem interfaces remain available.

- `thm_a_of_nondegenerate` needs nondegeneracy at the current basis;
  `thm_b_of_nondegenerate` needs it at the two endpoints of the pivot.
- `run_hat_of_nondegenerate` lifts a complete source run, with matching choices
  at each visited basis and exactly the same number of major cycles.
- `cap_partialRun_hat_iff` and `cap_run_hat_iff` preserve runs from corresponding
  starts, assuming an attained optimum and a feasible starting basis. No global
  nondegeneracy or rank premise is used. `isNondegenerate_hat_cap` preserves
  nondegeneracy at each visited basis, and `dantzig_hat_cap_iff` preserves choices.
- `capped_linopt_run_of_nondegenerate` composes these results. If the source
  entering choices are unique along the given run,
  `capped_linopt_run_matches_of_unique` proves that every complete linopt run
  from the corresponding corral has the same length and supports. The underlying
  `linopt_partialRun_matches_of_unique` also bounds every partial run by the
  length of the source run, so the complete-run statement is not the only
  guarantee provided.

The target in the capped transfer is `P.cap.atom`, with `n + 2` integer points
in dimension `m + 2`. Its start is the corral corresponding to the source basis,
not a singleton. The network and rational-data reductions below compose these
mathematical run/count transfers with explicit preprocessing.

## Capacity-slack conversion (Appendix C.4)

[`NetworkFlow.lean`](../WolfeSimplex/Proofs/NetworkFlow.lean) proves the algebraic
conversion for [`BoundedLP`](../WolfeSimplex/Defs/NetworkFlow.lean), whose state
includes a basis of the reduced conservation matrix, non-tree upper-bound arcs
and the actual feasible flow. It is included in the default library and audits.

- `lift_feasible_iff`, `standard_isBasis`, `standard_basicSol` and
  `standard_feasibleBasis` establish the capacity-slack feasible-point and basis
  correspondence. The standard LP has `m + n` rows and `2n` variables.
- `standard_nondegenerate` requires strictly interior tree flows **and positive
  capacities on every arc**. The latter condition is not inferred from tree
  nondegeneracy.
- `standard_basicDir`, `standard_reducedCost` and `standard_dantzig_iff` preserve
  oriented directions and Dantzig choices, including ties. An upper arc enters
  through its capacity slack, with the negated original reduced cost.
- `standard_isLeavingLabel_iff`, `basis_exchange`, `standard_pivot` and
  `standard_run` preserve ratio tests, bound flips, complete runs and their exact
  pivot counts. `standard_unique` preserves uniqueness of the entering choice.

The regression script checks concrete lower-to-upper and upper-to-lower bound
flips on two parallel arcs: their tree is unchanged, but their flows and active
bounds change. It also checks the upper slack's reduced-cost sign, Dantzig choices
and standard-basis nondegeneracy.

This conversion is one step in the conditional transfer development below.

## Corollary 4: checked reductions and executed preprocessing

The entry points are `PaperCorollary4.corollary4_queries` and
`PaperCorollary4.corollary4_count_extended` (or `corollary4_count` for already
finite capacities). These prove answer/count equivalences and
polynomial bounds on the reduction's measured resource costs. Native network
preprocessing now has explicit first-order programs with checked value and cost
certificates, including construction of the initial support.
The cited FS15/DS18 hardness proofs and a Turing-machine definition of NP/PSPACE
are deliberately outside the development. The new construction's correctness
and runtime certificates are proved here rather than assumed from the literature.

For the PSPACE parts, `QueryInput` contains an actual rational LP, a feasible
initial basis enumeration, its MDP column owners/sign pattern and an existing
complete source run. `MDPFeasibleBasis.nondegenerate_of_columnOwners` derives
global nondegeneracy from positive supplies and the off-owner sign pattern;
it is not an additional literature premise. `sourceCorrect` expresses FS15's
queried-variable answer for every Dantzig tie resolution. This robustness is
explicit in [FS15, Sections 1–2 and Appendix C](https://arxiv.org/html/1404.0605v2).
The initially-nonbasic restriction applies only to BasisEntry.

`QueryInstance.certificate` proves integrality, the unique shortest atom,
the answer equivalence under `IsIndexLinoptChoice`, and a uniform polynomial
construction budget. `QueryInput.trace` carries every target run through the
initial prefix to a rational Dantzig run. `queries` proves insertion and
final-support equivalences; the final-basis question also permits an initially
basic queried variable. `QueryEvents.exists_index_run` proves existence of a
complete fixed-index run, preventing vacuous universal correctness claims.
The target has `n+3` integer points in dimension `m+3`.

For counting, `NetworkInput` contains native endpoints, supplies, costs,
capacities, component roots/retained rows, an initial tree/bound state and the
native run promises of [DS18, Section 4](https://arxiv.org/html/1311.5935v2).
Positive capacities, strict interior tree flows along the run and uniqueness
of entering choices are separate premises. The source answer in
`corollary4_count` is the number of native pivots, not a standard-LP or Wolfe
count. `NetworkIncidence` proves balanced row deletion and derives incidence
column independence from fundamental-cut forest certificates. It relates
native fundamental cycles, reduced costs, ratio tests and actual flow updates
to the capacity-slack model, including bound flips. `deleteLast` supplies a
literal retained-row enumeration for the connected case.

DS18's published construction also has infinite-capacity outer arcs.
[`InfiniteCapacity`](../WolfeSimplex/Proofs/InfiniteCapacity.lean) models these
as absent upper bounds: they have no upper ratio-test candidate and cannot be
non-tree arcs at an upper bound. `ExtendedNetworkInput` accepts this original
native source model. Its `terminal` premise is a graph fact from DS18: each
uncapacitated arc has a tail with no incoming arcs or a head with no outgoing
arcs. Conservation and nonnegative flows then give a strict input-derived
bound, proved by `flow_lt_bound`. No maximum encountered flow is assumed.

The replacement is the positive integer `1 + sum |supply.num|`. Rational
denominators are at least one, so this bounds every absolute supply, and hence
every flow on an uncapacitated outer arc, strictly. `feasible_iff` preserves
feasibility. `pivot_to_finite` proves that every newly introduced upper ratio
is strictly beyond the actual native pivot endpoint; `run_to_finite` preserves
all visited states and the exact run length, including bound flips.
`nondegenerate_to_finite` proves the needed strict upper inequalities on tree
arcs. The old finite input is constructed internally by `normalize`.

[`Execution/InfiniteCapacity`](../WolfeSimplex/Execution/InfiniteCapacity.lean)
reads supply numerators, finite capacity data and absent-bound flags. It emits
the exact normalized capacity numerator/denominator arrays; endpoints, costs,
supplies and retained rows are shared unchanged. Its value, syntax, work,
numeric growth, addresses and measured bit-work bounds are checked.
[`InfiniteCapacityBounds`](../WolfeSimplex/Proofs/InfiniteCapacityBounds.lean)
proves polynomial normalized binary input size. The new
[`Corollary4InfiniteCapacity`](../WolfeSimplex/Proofs/Corollary4InfiniteCapacity.lean)
entry point composes both bounds with the existing executed reduction and
proves exact target counts directly from the original source run. Neither
finite replacement nor its correctness/cost is a literature premise.

`RationalPreprocess` clears entire rows and the entire objective with positive
denominator products. Its executable table/product program is proved equal to
the integerization, and preserves Dantzig choices, runs and basic solutions.
`RationalPreprocessBounds`, `Construction/Cap` and `Corollary4Resources` prove
uniform work, intermediate width, output coefficient/encoding and composed bit
bounds. `programs_correct` links the rational and cap programs to the existing
first-order integer atom/shield programs.

[`Execution/Network`](../WolfeSimplex/Execution/Network.lean) implements native
network conversion in the existing first-order interpreter. Endpoints and
retained row indices are read as input arrays. Equality is computed from integer
subtraction and sign, and selecting a retained supply row is an executed scan;
no input-dependent selection is hidden in program generation. The program emits
the exact six arrays of rational numerators/denominators consumed by integerization.
`NetworkBounds` proves syntax size, work, intermediate width, address bounds and
bit work. `NetworkMask` computes the exact two-times-lifted initial basis mask
from the tree/upper-bound flag arrays and proves its work and width bounds.
`RationalNetwork.preparation_certificate` combines value correctness with a
polynomial bound on these programs' interpreted bit work. The reduction's
`preparationCost` now equals that measured cost, with no reported polynomial
charge substituted for execution. Numeric construction uses
the documented arithmetic/array cost semantics, not Lean's compiled runtime.
Dimension headers in the new encodings are unary and linear in the explicit
dense/network data; numerators, denominators and endpoints are binary.

`NetworkInput.count_transfer` proves that a complete fixed-index target run
exists and every such run has exactly the native pivot count. The target is
`2n+2` integer points in dimension `m+n+2`, started from the corresponding
corral. Neither target construction reads a source run or its unknown length.
The family theorems compose these executed costs with the polynomial size bounds
of the external source families. They do not assume the new reduction or its
polynomial cost as a literature premise. `NetworkInput.preprocessing_certificate`
links the executed data and support to the objects in the mathematical transfer.

The regression scripts cover parallel arcs and deleted conservation rows,
capacity-bound flips, nontrivial rational denominator clearing, a one-pivot
count transfer, both positive queried events, and a negative final query on
an initially basic variable. The native preprocessing regression executes
permuted retained rows, a self-loop, both incidence signs, rational denominators
and upper-bound support flags, and checks the returned arrays and measured peaks.

## Checks

After `lake exe cache get`, run `sh scripts/check.sh` from the repo root. It runs:

| Command | Purpose |
|---|---|
| `lake build` | Compile the library and check its proof terms |
| `lake env lean scripts/CheckAxioms.lean` | Reject unexpected axioms in every declaration owned by imported project modules, including private helpers |
| `lake env lean scripts/CheckPaperPath.lean` | Check selected proof dependencies and the main statement's definition boundary |
| `lake env lean scripts/CheckConstruction.lean` | Evaluate an admissible example, including a negative coordinate, operation count and input length |
| `lake env lean scripts/CheckEfficiency.lean` | Check support projection and entering-label extraction on a one-pivot fixture |
| `lake env lean scripts/CheckExecution.lean` | Exercise signed determinants, both preparations, branching, indexed memory and division |
| `lake env lean scripts/CheckRunLocal.lean` | Apply the run-local and capped transfers to an LP with a degenerate feasible basis outside its chosen run |
| `lake env lean scripts/CheckNetworkFlow.lean` | Check upper-bound entry, both directions of a bound flip, reduced-cost signs and nondegeneracy |
| `lake env lean scripts/CheckNetworkIncidence.lean` | Derive a parallel-arc incidence basis from cuts and verify the deleted conservation row |
| `lake env lean scripts/CheckCorollary4.lean` | Check rational preprocessing, a one-pivot count transfer and positive/negative shortest-start queried events |
| `lake env lean scripts/CheckNetworkPreparation.lean` | Execute native network conversion and initial-mask construction; check permuted rows, loops, rational data and measured peaks |
| `lake env lean scripts/CheckTable1.lean` | Check exact rate/count examples and a concrete rational MDP's derived nondegeneracy, integer data, atom output and initial support |
| `lake env lean scripts/CheckInfiniteCapacity.lean` | Preserve a native pivot on an uncapacitated entering arc with a zero placeholder; check exact Wolfe count, rational arrays, measured peaks and a nonterminal circulation counterexample |

All must exit successfully. The example is a smoke check; universal construction
claims are theorems. Individual commands show full output. Module-system, style
and deprecation warnings occur with the pinned Lean/Mathlib versions.

## Alignment record

The current statement audit uses the manuscript with SHA-256
`9c07b865c767b30dba9bb00407efa6aeafe80311934d92a62801e1b1b69a13e4`.
This hash was measured from the unchanged downloaded archive on 10 November
2026; it replaces the older manuscript hash in this guide.
An assistant compared the 55 public statements and supporting definitions at
`bc493cbcb1c751e97ec60f985dd1fed9d17b5a7b` on 9 November 2026. Later revisions
added the `D` minor-cycle bound, composed paper path, binary lengths, executable
construction, complete shortest-start resource certificates, the iteration and
measured-procedure versions of Corollary 1, and all Corollary 2 family transfers
relative to the stated literature inputs. This record
is not independent human certification; author sign-off on definitions and statements remains pending.
The manuscript itself is not distributed in this repo.

On 10 November 2026, the conditional Corollary 4 reduction chain and both new
regression scripts were added. The expanded ten-check suite passed with the
new modules imported by the default library. The five external manuscript
source files were checked against the downloaded archive and remained identical.

The final [coverage record](COVERAGE.md) includes all 26 numbered statement
blocks, Table 1, algorithm/initialization claims and construction costs. The
quantitative randomized corollaries and concrete polynomial source-to-target
construction were added to the default imports and checks.
The integrated twelve-check suite passed on 10 November 2026, including the
whole-project axiom audit and quantitative/construction proof-dependency checks.
All five external manuscript sources still match the downloaded archive.

The later submission review identified an implicit source-normalization step:
DS18 uses infinite capacities, while the earlier source interface accepted only
finite ones. This is now a proved preprocessing step with an absent-bound native
source semantics, executed numeric arrays, polynomial resources and a direct
Corollary 4 family theorem. The earlier finite-capacity theorem remains available.
The expanded thirteen-check suite passed, including the new native
infinite-capacity regression, the full axiom audit and the normalization/cost
proof-dependency checks. The manuscript snapshots remain unchanged.
