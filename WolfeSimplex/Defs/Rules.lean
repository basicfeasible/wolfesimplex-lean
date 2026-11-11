import WolfeSimplex.Defs.Simplex
import WolfeSimplex.Defs.Wolfe

/-!
# Pivot rules and insertion rules (paper: Table 1 (`tab:wolfe-rules`), Section 2.2 (`sec:wolfe`))

Trusted definitions of the rules used in Appendix C.2 (`app:cor-rules`) (shortest-atom construction)
(Lemma 14 (`lem:init-run`),
Lemma 17 (`lem:minnorm`), Lemma 18 (`lem:km-start`), Lemma 15 (`lem:km`)).

## How rules and ties are modeled

A rule is modeled by the *set of choices it allows*: a predicate `choice B j`
saying that the rule may choose the label `j` at the current basis (or corral) `B`.
If several labels tie, all of them are allowed. A run *with* a rule is then a run in
which every step makes an allowed choice. A statement "for every rule for breaking
ties, the run has property X" becomes "every run with the rule has property X".

Only rules that depend on the current basis (or corral) alone are needed here
(Dantzig, Bland, linopt, least label, minnorm).

Orders of the labels are given by a *rank function* `r : Fin n → ℕ`
(`i` comes before `j` iff `r i < r j`).
-/

namespace WolfeSimplex

open Finset Matrix

namespace LP

variable {m n : ℕ} (P : LP m n)

/-- Dantzig's rule may enter `j` at the basis `B` (paper: Table 1 (`tab:wolfe-rules`)):
`j` is improving and has the most negative reduced cost among the improving labels. -/
def IsDantzigChoice (B : Finset (Fin n)) (j : Fin n) : Prop :=
  j ∈ P.improving B ∧ ∀ i ∈ P.improving B, P.reducedCost B j ≤ P.reducedCost B i

/-- Bland's rule for the order given by the rank function `r` may enter `j` at the
basis `B` (paper: Table 1 (`tab:wolfe-rules`)): `j` is the improving label that comes
first in the order. -/
def IsBlandChoice (r : Fin n → ℕ) (B : Finset (Fin n)) (j : Fin n) : Prop :=
  j ∈ P.improving B ∧ ∀ i ∈ P.improving B, r j ≤ r i

/-- `B 0, …, B f` is a *partial* simplex run with the rule `choice` (of length `f`):
all `B k` are feasible bases, and each `B (k+1)` arises from `B k` by the pivot on a
label `j` that the rule may choose at `B k`. (Unlike `IsSimplexRun`, the last basis
may still have improving labels: this is the beginning of a run.) -/
def IsPartialSimplexRunWith (choice : Finset (Fin n) → Fin n → Prop) (f : ℕ)
    (B : ℕ → Finset (Fin n)) : Prop :=
  (∀ k ≤ f, P.IsFeasibleBasis (B k)) ∧
  ∀ k < f, ∃ j, choice (B k) j ∧ P.IsPivot (B k) j (B (k + 1))

/-- `B 0, …, B f` is a simplex run with the rule `choice`: a partial run with the
rule whose last basis `B f` has no improving label (compare `IsSimplexRun`). -/
def IsSimplexRunWith (choice : Finset (Fin n) → Fin n → Prop) (f : ℕ)
    (B : ℕ → Finset (Fin n)) : Prop :=
  P.IsPartialSimplexRunWith choice f B ∧ P.improving (B f) = ∅

end LP

namespace Wolfe

variable {n D : ℕ} (p : Fin n → Fin D → ℝ)

/-- Wolfe's linopt rule may insert `j` at the corral `S` (paper: Section 2.2 (`sec:wolfe`)): `j`
is improving at `w_S` and minimizes `p_jᵀ w_S` among the improving
labels (equivalently, it has minimum gap). -/
def IsLinoptChoice (S : Finset (Fin n)) (j : Fin n) : Prop :=
  j ∈ improving p (affineMin p S) ∧
    ∀ i ∈ improving p (affineMin p S), p j ⬝ᵥ affineMin p S ≤ p i ⬝ᵥ affineMin p S

/-- The minnorm rule may insert `j` at the corral `S` (paper: Section 2.2 (`sec:wolfe`)):
`j` is improving at `w_S` and has minimum norm `‖p_j‖` among the improving labels. -/
def IsMinnormChoice (S : Finset (Fin n)) (j : Fin n) : Prop :=
  j ∈ improving p (affineMin p S) ∧
    ∀ i ∈ improving p (affineMin p S), normSq (p j) ≤ normSq (p i)

/-- The least-label rule for the order given by the rank function `r` may insert `j`
at the corral `S` (paper: Table 1 (`tab:wolfe-rules`)): `j` is the improving label that
comes first in the order. -/
def IsLeastLabelChoice (r : Fin n → ℕ) (S : Finset (Fin n)) (j : Fin n) : Prop :=
  j ∈ improving p (affineMin p S) ∧ ∀ i ∈ improving p (affineMin p S), r j ≤ r i

/-- `S 0, …, S f` is a *partial* Wolfe run with the insertion rule `choice` (of
length `f`): all `S k` are corrals, and each `S (k+1)` is the corral at the end of a
major cycle at `S k` that inserts a label `j` that the rule may choose at `S k`.
(The last corral may still have improving atoms: this is the beginning of a run.) -/
def IsPartialWolfeRunWith (choice : Finset (Fin n) → Fin n → Prop) (f : ℕ)
    (S : ℕ → Finset (Fin n)) : Prop :=
  (∀ k ≤ f, IsCorral p (S k)) ∧
  ∀ k < f, ∃ j, choice (S k) j ∧ MajorCycle p (S k) j (S (k + 1))

/-- `S 0, …, S f` is a Wolfe run with the insertion rule `choice`: a partial run with
the rule such that no atom is improving at the affine minimizer of the last corral
(compare `IsWolfeRun`). -/
def IsWolfeRunWith (choice : Finset (Fin n) → Fin n → Prop) (f : ℕ)
    (S : ℕ → Finset (Fin n)) : Prop :=
  IsPartialWolfeRunWith p choice f S ∧ improving p (affineMin p (S f)) = ∅

end Wolfe

end WolfeSimplex
