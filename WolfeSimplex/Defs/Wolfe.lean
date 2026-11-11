import Mathlib

/-!
# Wolfe's minimum-norm-point method (paper: Section 2.2 (`sec:wolfe`))

Trusted definitions for Wolfe's method, following Section 2.2 (`sec:wolfe`),
Definition 2 (`def:gap`) and Algorithm 2 (`alg:wolfe`) of the paper.

## Conventions

* The atoms are `p : Fin n → (Fin D → ℝ)`, i.e. `n` points `p j ∈ ℝ^D`, with labels
  `Fin n = {0, …, n-1}`.
* `‖·‖` is the Euclidean norm. To avoid any confusion with other norms, we only
  use the squared Euclidean norm `normSq w = wᵀw = ‖w‖²`; minimizing `‖·‖` and
  minimizing `‖·‖²` is the same.
* Coefficient vectors `λ ∈ ℝ^S` are functions `Fin n → ℝ` that vanish outside `S`
  (extension by zeros, as in the paper). `λ` is a reserved word in Lean, so we
  write `lam`.
* As in `Defs/Simplex.lean`, `Classical.epsilon p` is "some element satisfying
  `p`". In all states that the algorithm can reach, that element is unique
  (supports are nonempty and affinely independent there); other values are never
  used by the main results.
-/

namespace WolfeSimplex

namespace Wolfe

open Finset Matrix

variable {n D : ℕ} (p : Fin n → Fin D → ℝ)

/-- The squared Euclidean norm `‖w‖² = wᵀw`. -/
def normSq (w : Fin D → ℝ) : ℝ := w ⬝ᵥ w

/-- The atoms `p_i`, `i ∈ S`, are affinely independent (paper: Notation,
`sec:notation`): `∑_{i∈S} β_i p_i = 0` and `∑_{i∈S} β_i = 0` imply `β_i = 0` for
all `i ∈ S`. -/
def IsAffinelyIndependent (S : Finset (Fin n)) : Prop :=
  ∀ β : Fin n → ℝ, ∑ i ∈ S, β i • p i = 0 → ∑ i ∈ S, β i = 0 → ∀ i ∈ S, β i = 0

/-- The affine hull `aff(S)` of the atoms `p_i`, `i ∈ S`. -/
def affineHull (S : Finset (Fin n)) : Set (Fin D → ℝ) :=
  {x | ∃ lam : Fin n → ℝ, ∑ i ∈ S, lam i = 1 ∧ x = ∑ i ∈ S, lam i • p i}

/-- The convex hull `conv(S)` of the atoms `p_i`, `i ∈ S`. -/
def convexHull (S : Finset (Fin n)) : Set (Fin D → ℝ) :=
  {x | ∃ lam : Fin n → ℝ, (∀ i ∈ S, 0 ≤ lam i) ∧ ∑ i ∈ S, lam i = 1 ∧
    x = ∑ i ∈ S, lam i • p i}

/-- The defining property of the affine minimizer: `w ∈ aff(S)` has minimum
Euclidean norm on `aff(S)`. -/
def IsAffineMinimizerOf (S : Finset (Fin n)) (w : Fin D → ℝ) : Prop :=
  w ∈ affineHull p S ∧ ∀ x ∈ affineHull p S, normSq w ≤ normSq x

/-- The affine minimizer `w_S = argmin_{x ∈ aff(S)} ‖x‖` of a support `S`
(paper: Section 2.2 (`sec:wolfe`); the minimizing point is unique for every nonempty
`S`). -/
noncomputable def affineMin (S : Finset (Fin n)) : Fin D → ℝ :=
  Classical.epsilon (IsAffineMinimizerOf p S)

/-- The defining property of the coefficients `λ^{*S}` of the affine minimizer:
`λ` vanishes outside `S`, `∑_{i∈S} λ_i = 1`, and `∑_{i∈S} λ_i p_i = w_S`. -/
def IsAffineCoeffsOf (S : Finset (Fin n)) (lam : Fin n → ℝ) : Prop :=
  (∀ i ∉ S, lam i = 0) ∧ ∑ i ∈ S, lam i = 1 ∧ ∑ i ∈ S, lam i • p i = affineMin p S

/-- The coefficients `λ^{*S}` of the affine minimizer `w_S` (paper: Section 2.2 (`sec:wolfe`);
unique for affinely independent `S`). -/
noncomputable def affineCoeffs (S : Finset (Fin n)) : Fin n → ℝ :=
  Classical.epsilon (IsAffineCoeffsOf p S)

/-- `S` is a corral: a nonempty, affinely independent support whose affine
minimizer has positive coefficients `λ^{*S}_i > 0` for all `i ∈ S`
(paper: Section 2.2 (`sec:wolfe`)). -/
def IsCorral (S : Finset (Fin n)) : Prop :=
  S.Nonempty ∧ IsAffinelyIndependent p S ∧ ∀ i ∈ S, 0 < affineCoeffs p S i

/-- The gap `g_j(w) = p_jᵀw - ‖w‖²` of atom `j` at the point `w`
(paper: Definition 2 (`def:gap`)). -/
def gap (j : Fin n) (w : Fin D → ℝ) : ℝ := p j ⬝ᵥ w - normSq w

/-- The set `Γ(w) = {j : g_j(w) < 0}` of atoms that are improving at `w`
(paper: Definition 2 (`def:gap`)). -/
noncomputable def improving (w : Fin D → ℝ) : Finset (Fin n) :=
  univ.filter (fun j ↦ gap p j w < 0)

/-- `w` is the optimal solution of the minimum-norm-point problem
`min ‖w‖ subject to w ∈ conv{p_1, …, p_n}` (paper: (MNP), `eq:mnp`). -/
def IsMinNormPoint (w : Fin D → ℝ) : Prop :=
  w ∈ convexHull p univ ∧ ∀ x ∈ convexHull p univ, normSq w ≤ normSq x

/-- A state of Algorithm 2 (`alg:wolfe`) inside a major cycle: the current support `S`
and the current coefficient vector `λ`. (That `λ ≥ 0` and `λ` vanishes outside `S`
is not part of the type; it holds in every state the algorithm reaches.) -/
structure State (n : ℕ) where
  /-- the current support -/
  S : Finset (Fin n)
  /-- the current coefficients -/
  lam : Fin n → ℝ

/-- The step length `t = max {r ∈ [0,1] : λ + r d ≥ 0}` (paper: Line `line:wf-step`
of Algorithm 2 (`alg:wolfe`)). Written as a supremum; for `λ ≥ 0` the set contains `0`,
is closed and lies in `[0,1]`, so the supremum is the maximum. -/
noncomputable def stepLength (lam d : Fin n → ℝ) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧ ∀ k, 0 ≤ lam k + r * d k}

/-- One minor cycle (paper: Lines `line:wf-loop`–`line:wf-delete` of Algorithm 2 (`alg:wolfe`)),
from state `s` to state `s'`: it is only performed if `s.S` is not a
corral; then `d = λ^{*S} - λ`, `t = stepLength λ d`, the new coefficients are
`λ + t d`, and ONE label `i ∈ S` whose new coefficient is zero is deleted
(any such `i`; the choice is free). -/
def MinorCycle (s s' : State n) : Prop :=
  ¬ IsCorral p s.S ∧
  s'.lam = s.lam + stepLength s.lam (affineCoeffs p s.S - s.lam) • (affineCoeffs p s.S - s.lam) ∧
  ∃ i ∈ s.S, s'.lam i = 0 ∧ s'.S = s.S.erase i

/-- A major cycle at the corral `S` that inserts the atom `j` and ends at the
corral `S'` (paper: Lines `line:wf-choose`–`line:wf-accept` of Algorithm 2 (`alg:wolfe`)): `j` is
improving at `w_S`; after inserting `j` with coefficient `0`
(start state `(S ∪ {j}, λ^{*S})`), a finite sequence of minor cycles (possibly
none) leads to the support `S'`, which is a corral. Since a minor cycle is only
performed at a non-corral, the minor cycles stop exactly at the first corral, as
in the `while` loop of the algorithm. The acceptance step (Line `line:wf-accept`)
then sets `λ = λ^{*S'}` and does not change the support. -/
def MajorCycle (S : Finset (Fin n)) (j : Fin n) (S' : Finset (Fin n)) : Prop :=
  IsCorral p S ∧ j ∈ improving p (affineMin p S) ∧
    ∃ lam' : Fin n → ℝ,
      Relation.ReflTransGen (MinorCycle p) ⟨insert j S, affineCoeffs p S⟩ ⟨S', lam'⟩ ∧
      IsCorral p S'

/-- `S 0, S 1, …, S f` is a Wolfe run (of length `f`) from `S 0`
(paper: definition at the end of Section 2.2 (`sec:wolfe`)): all `S k` are corrals,
each `S (k+1)` is the corral at the end of a major cycle at `S k`, and no atom is
improving at the affine minimizer of the last corral `S f`. Values `S k` for
`k > f` are irrelevant. -/
def IsWolfeRun (f : ℕ) (S : ℕ → Finset (Fin n)) : Prop :=
  (∀ k ≤ f, IsCorral p (S k)) ∧
  (∀ k < f, ∃ j, MajorCycle p (S k) j (S (k + 1))) ∧
  improving p (affineMin p (S f)) = ∅

end Wolfe

end WolfeSimplex
