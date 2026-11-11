import WolfeSimplex.Defs.Rules

/-!
# Randomized pivot and insertion rules (paper: Table 1 (`tab:wolfe-rules`), Table 1
(`tab:wolfe-rules`))

Trusted definitions for Corollary 2 (`cor:intro-rules`): Random-Edge and Random-Bland, and the
corresponding random and random-order insertion rules. The paper's claim for these rules is
that the runs agree *in distribution*.

## How random runs are modeled

* Probability distributions are Mathlib's `PMF α` (probability mass functions on `α`).
  `PMF.pure a` is the point mass at `a`; `p.bind f` first draws `a` from `p` and then draws
  from `f a`; `p.map g` is the distribution of `g a` for `a` drawn from `p`;
  `uniformOn s h` (defined below) is the uniform distribution on a nonempty finite set `s`.
  (This Mathlib version no longer has a uniform `PMF`, so it is defined here.)
* A randomized rule gives, at every basis (corral) with an improving label, a distribution on
  the labels to enter (insert).
* The result of the pivot on `j` at `B` is written `pivotTo B j`: *some* `B'` with
  `IsPivot B j B'`. Under the paper's assumptions this `B'` is unique (this is part of the
  statement `rules_unique_steps` in `MainResults`), so nothing is chosen. Likewise,
  `majorTo S j` is *some* corral at the end of a major cycle at `S` that inserts `j`; it is
  unique at the corrals `B̂` of the induced atoms (`rules_unique_steps`).
* `randomRun rule k B` is the distribution of the list of bases `[B 0, B 1, …]` visited in the
  first `k` pivots of the run from `B 0 = B` with the randomized rule: one basis, plus one
  more for each pivot; the list ends early (after `B f`) if the run stops at a basis `B f`
  without improving labels.
-/

namespace WolfeSimplex

open Finset

/-- The uniform distribution on the nonempty finite set `s`: every element of `s` has
probability `1/|s|`, every other element probability `0`. -/
noncomputable def uniformOn {α : Type*} [DecidableEq α] (s : Finset α) (h : s.Nonempty) : PMF α :=
  PMF.ofFinset (fun a ↦ if a ∈ s then ((s.card : ENNReal))⁻¹ else 0) s
    (by
      rw [Finset.sum_congr rfl fun a ha ↦ ite_eq_left ha, Finset.sum_const, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (by simpa using h.ne_empty) (ENNReal.natCast_ne_top _))
    (fun a ha ↦ ite_eq_right ha)

/-- The element of the nonempty set `s` that comes first in the order given by the
permutation `π` (`i` before `j` iff `π i < π j`), i.e. `argmin {π i : i ∈ s}`. -/
def firstInOrder {n : ℕ} (π : Equiv.Perm (Fin n)) (s : Finset (Fin n)) (h : s.Nonempty) : Fin n :=
  π.symm ((s.map π.toEmbedding).min' (h.map))

namespace LP

variable {m n : ℕ} (P : LP m n)

/-- The basis after the pivot on `j` at `B`: some `B'` with `IsPivot B j B'` (unique under
the paper's assumptions, see `rules_unique_steps`). -/
noncomputable def pivotTo (B : Finset (Fin n)) (j : Fin n) : Finset (Fin n) :=
  Classical.epsilon (P.IsPivot B j)

/-- The distribution of the list of bases visited in the first `k` pivots of the simplex
method from `B` with the randomized pivot rule `rule` (see the module docstring). -/
noncomputable def randomRun (rule : (B : Finset (Fin n)) → (P.improving B).Nonempty → PMF (Fin n)) :
    ℕ → Finset (Fin n) → PMF (List (Finset (Fin n)))
  | 0, B => PMF.pure [B]
  | k + 1, B =>
    if h : (P.improving B).Nonempty then
      (rule B h).bind fun j ↦ (randomRun rule k (P.pivotTo B j)).map (List.cons B)
    else PMF.pure [B]

/-- Random-Edge (paper: Table 1 (`tab:wolfe-rules`)): enter a uniformly random improving label. -/
noncomputable def randomEdge (B : Finset (Fin n)) (h : (P.improving B).Nonempty) : PMF (Fin n) :=
  uniformOn (P.improving B) h

/-- Bland's rule for the order given by the permutation `π`, as a (deterministic) randomized
rule: enter the improving label that comes first in the order. -/
noncomputable def blandBy (π : Equiv.Perm (Fin n)) (B : Finset (Fin n))
    (h : (P.improving B).Nonempty) : PMF (Fin n) :=
  PMF.pure (firstInOrder π (P.improving B) h)

/-- Random-Bland (paper: Table 1 (`tab:wolfe-rules`)): draw a uniformly random permutation `π` of
the labels once, then run Bland's rule for the order `π`. The distribution of the list of
bases visited in the first `k` pivots from `B`. -/
noncomputable def randomBlandRun (k : ℕ) (B : Finset (Fin n)) : PMF (List (Finset (Fin n))) :=
  (uniformOn (univ : Finset (Equiv.Perm (Fin n))) univ_nonempty).bind fun π ↦
    P.randomRun (P.blandBy π) k B

end LP

namespace Wolfe

variable {n D : ℕ} (p : Fin n → Fin D → ℝ)

/-- The corral at the end of a major cycle at `S` that inserts `j`: some `S'` with
`MajorCycle p S j S'` (unique at the corrals `B̂` of the induced atoms, see
`rules_unique_steps`). -/
noncomputable def majorTo (S : Finset (Fin n)) (j : Fin n) : Finset (Fin n) :=
  Classical.epsilon (MajorCycle p S j)

/-- The distribution of the list of corrals visited in the first `k` major cycles of Wolfe's
method from `S` with the randomized insertion rule `rule` (see the module docstring). -/
noncomputable def randomRun
    (rule : (S : Finset (Fin n)) → (improving p (affineMin p S)).Nonempty → PMF (Fin n)) :
    ℕ → Finset (Fin n) → PMF (List (Finset (Fin n)))
  | 0, S => PMF.pure [S]
  | k + 1, S =>
    if h : (improving p (affineMin p S)).Nonempty then
      (rule S h).bind fun j ↦ (randomRun rule k (majorTo p S j)).map (List.cons S)
    else PMF.pure [S]

/-- The random insertion rule (paper: Table 1 (`tab:wolfe-rules`)): insert a uniformly random
improving atom. -/
noncomputable def randomInsertion (S : Finset (Fin n))
    (h : (improving p (affineMin p S)).Nonempty) : PMF (Fin n) :=
  uniformOn (improving p (affineMin p S)) h

/-- The least-label rule for the order given by the permutation `π`, as a (deterministic)
randomized rule: insert the improving atom whose label comes first in the order. -/
noncomputable def leastLabelBy (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (h : (improving p (affineMin p S)).Nonempty) : PMF (Fin n) :=
  PMF.pure (firstInOrder π (improving p (affineMin p S)) h)

/-- The random-order rule (paper: Table 1 (`tab:wolfe-rules`)): draw a uniformly random permutation
`π` of the labels once, then run the least-label rule for the order `π`. The distribution of
the list of corrals visited in the first `k` major cycles from `S`. -/
noncomputable def randomOrderRun (k : ℕ) (S : Finset (Fin n)) : PMF (List (Finset (Fin n))) :=
  (uniformOn (univ : Finset (Equiv.Perm (Fin n))) univ_nonempty).bind fun π ↦
    randomRun p (leastLabelBy p π) k S

end Wolfe

end WolfeSimplex
