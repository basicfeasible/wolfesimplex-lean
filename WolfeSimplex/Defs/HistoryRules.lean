import WolfeSimplex.Defs.Rules

/-!
# History-dependent pivot and insertion rules (paper: Table 1 (`tab:wolfe-rules`), Table 1
(`tab:wolfe-rules`))

Trusted definitions for Corollary 2 (`cor:intro-rules`): Zadeh's and Cunningham's pivot rules and
the
corresponding least-inserted and round-robin insertion rules. These rules depend on the
*history* of the run: on the labels that entered (were inserted) so far.

## How runs with a history are modeled

A run now consists of the bases (corrals) `B 0, …, B f` *and* the labels `J 0, …, J (f-1)`,
where `J k` is the label that enters (is inserted) at step `k`, i.e. at `B k`. In the paper's
notation, `J k = j_{k+1}`, and at the basis `B k` the labels `j_1, …, j_k` that entered so far
are the list `[J 0, …, J (k-1)]` (`(List.range k).map J`). A rule is again modeled by the set
of choices it allows: `choice hist B j` says that the rule may choose `j` at `B` when the
labels that entered so far are the list `hist`. Ties allow all tied labels.
-/

namespace WolfeSimplex

open Finset

/-- The cyclic distance `(b - a) mod n` from `a` to `b` in `Fin n` (paper: Table 1
(`tab:wolfe-rules`) and Table 1 (`tab:wolfe-rules`), `(i - j_k) mod n`). -/
def cyclicDist {n : ℕ} (a b : Fin n) : ℕ := ((b : ℕ) + n - (a : ℕ)) % n

namespace LP

variable {m n : ℕ} (P : LP m n)

/-- `B 0, …, B f` with the entering labels `J 0, …, J (f-1)` is a *partial* simplex run with the
history-dependent rule `choice`: all `B k` are feasible bases, and each `B (k+1)` arises from
`B k` by the pivot on the label `J k`, which the rule may choose at `B k` given the labels
`[J 0, …, J (k-1)]` that entered before. -/
def IsPartialSimplexRunWithHist (choice : List (Fin n) → Finset (Fin n) → Fin n → Prop) (f : ℕ)
    (B : ℕ → Finset (Fin n)) (J : ℕ → Fin n) : Prop :=
  (∀ k ≤ f, P.IsFeasibleBasis (B k)) ∧
  ∀ k < f, choice ((List.range k).map J) (B k) (J k) ∧ P.IsPivot (B k) (J k) (B (k + 1))

/-- A simplex run with the history-dependent rule `choice`: a partial run whose last basis has
no improving label. -/
def IsSimplexRunWithHist (choice : List (Fin n) → Finset (Fin n) → Fin n → Prop) (f : ℕ)
    (B : ℕ → Finset (Fin n)) (J : ℕ → Fin n) : Prop :=
  P.IsPartialSimplexRunWithHist choice f B J ∧ P.improving (B f) = ∅

/-- Zadeh's rule may enter `j` at `B`, when the labels `hist` entered so far (paper: Table 1
(`tab:wolfe-rules`)): `j` is improving and has entered least often among the improving labels. -/
def IsZadehChoice (hist : List (Fin n)) (B : Finset (Fin n)) (j : Fin n) : Prop :=
  j ∈ P.improving B ∧ ∀ i ∈ P.improving B, hist.count j ≤ hist.count i

/-- Cunningham's rule with the initial label `j₀` may enter `j` at `B`, when the labels `hist`
entered so far (paper: Table 1 (`tab:wolfe-rules`)): `j` is improving and minimizes
`(i - j_k) mod n` over the improving labels `i`, where `j_k` is the last label that entered
(`j₀` if none has entered yet). -/
def IsCunninghamChoice (j₀ : Fin n) (hist : List (Fin n)) (B : Finset (Fin n)) (j : Fin n) :
    Prop :=
  j ∈ P.improving B ∧
    ∀ i ∈ P.improving B, cyclicDist (hist.getLastD j₀) j ≤ cyclicDist (hist.getLastD j₀) i

end LP

namespace Wolfe

variable {n D : ℕ} (p : Fin n → Fin D → ℝ)

/-- `S 0, …, S f` with the inserted labels `J 0, …, J (f-1)` is a *partial* Wolfe run with the
history-dependent insertion rule `choice`: all `S k` are corrals, and each `S (k+1)` is the
corral at the end of a major cycle at `S k` that inserts `J k`, which the rule may choose at
`S k` given the labels `[J 0, …, J (k-1)]` inserted before. -/
def IsPartialWolfeRunWithHist (choice : List (Fin n) → Finset (Fin n) → Fin n → Prop) (f : ℕ)
    (S : ℕ → Finset (Fin n)) (J : ℕ → Fin n) : Prop :=
  (∀ k ≤ f, IsCorral p (S k)) ∧
  ∀ k < f, choice ((List.range k).map J) (S k) (J k) ∧ MajorCycle p (S k) (J k) (S (k + 1))

/-- A Wolfe run with the history-dependent insertion rule `choice`: a partial run such that no
atom is improving at the affine minimizer of the last corral. -/
def IsWolfeRunWithHist (choice : List (Fin n) → Finset (Fin n) → Fin n → Prop) (f : ℕ)
    (S : ℕ → Finset (Fin n)) (J : ℕ → Fin n) : Prop :=
  IsPartialWolfeRunWithHist p choice f S J ∧ improving p (affineMin p (S f)) = ∅

/-- The least-inserted rule may insert `j` at the corral `S`, when the labels `hist` were
inserted so far (paper: Table 1 (`tab:wolfe-rules`)): `j` is improving at `w_S` and has been
inserted least often among the improving labels. -/
def IsLeastInsertedChoice (hist : List (Fin n)) (S : Finset (Fin n)) (j : Fin n) : Prop :=
  j ∈ improving p (affineMin p S) ∧
    ∀ i ∈ improving p (affineMin p S), hist.count j ≤ hist.count i

/-- The round-robin rule with the initial label `j₀` may insert `j` at the corral `S`, when the
labels `hist` were inserted so far (paper: Table 1 (`tab:wolfe-rules`)): `j` is improving at `w_S`
and minimizes `(i - j_k) mod n` over the improving labels `i` (here `n` is the number of
atoms), where `j_k` is the last inserted label (`j₀` if none was inserted yet). -/
def IsRoundRobinChoice (j₀ : Fin n) (hist : List (Fin n)) (S : Finset (Fin n)) (j : Fin n) :
    Prop :=
  j ∈ improving p (affineMin p S) ∧
    ∀ i ∈ improving p (affineMin p S),
      cyclicDist (hist.getLastD j₀) j ≤ cyclicDist (hist.getLastD j₀) i

end Wolfe

end WolfeSimplex
