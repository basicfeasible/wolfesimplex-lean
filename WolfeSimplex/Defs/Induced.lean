import WolfeSimplex.Defs.Simplex
import WolfeSimplex.Defs.Wolfe

/-!
# Admissible LPs, the induced LP, and the induced atoms (paper: Section 3 (`sec:equivalence`))

Trusted definitions for Section 3 (`sec:equivalence`) of the paper: admissible linear
programs (assumptions (A1)–(A3)), the numbers `U, T, C, K, H, N`, the induced
linear program (LP_λ) (`eq:induced-lp`), the atoms `p_j` (Equation 12 (`eq:atoms`)), and the
map `B ↦ B̂ = B ∪ {n+1}`.

## Conventions

* (A1) is built into the data type: an `IntLP` has integer data `A, b, c`.
  `IntLP.toLP` is the same LP read over `ℝ`.
* Labels of the induced LP are `Fin (n+1) = {0, …, n}`. The original label
  `j : Fin n` is `Fin.castSucc j` (same number), and the slack label (the paper's
  `n+1`) is `Fin.last n` (the number `n`).
* Coordinates of `ℝ^{m+1}` (where the atoms live) are `Fin (m+1) = {0, …, m}`.
  Coordinate `0` is the cost coordinate (the paper's coordinate `1`), and
  coordinates `1, …, m` are the constraint coordinates (the paper's `2, …, m+1`).
* `Fin.snoc v x` is the vector `v` with the entry `x` appended at the end, and
  `Fin.cons x v` is the vector `v` with the entry `x` put in front.
-/

namespace WolfeSimplex

open Finset Matrix

/-- A linear program `min cᵀx, Ax = b, x ≥ 0` with integer data
(paper: (LP) with assumption (A1), `ass:integral`). -/
structure IntLP (m n : ℕ) where
  /-- the constraint matrix `A ∈ ℤ^{m×n}` -/
  A : Matrix (Fin m) (Fin n) ℤ
  /-- the right-hand side `b ∈ ℤ^m` -/
  b : Fin m → ℤ
  /-- the cost vector `c ∈ ℤⁿ` -/
  c : Fin n → ℤ

namespace IntLP

variable {m n : ℕ} (P : IntLP m n)

/-- The same linear program, with the integer data read as real numbers. -/
def toLP : LP m n where
  A := P.A.map (fun a ↦ (a : ℝ))
  b := fun i ↦ (P.b i : ℝ)
  c := fun j ↦ (P.c j : ℝ)

/-- The LP is admissible (paper: beginning of Section 3 (`sec:equivalence`)):
it is an LP as in Section 2.1 (`sec:simplex`), i.e. `A` has rank `m ≥ 1`, and
(A1) the data are integral (built into `IntLP`),
(A2) the feasible set is nonempty and bounded,
(A3) every feasible basis is nondegenerate. -/
def IsAdmissible : Prop :=
  1 ≤ m ∧ P.toLP.A.rank = m ∧
  P.toLP.FeasibleSetNonemptyBounded ∧
  ∀ B, P.toLP.IsFeasibleBasis B → P.toLP.IsNondegenerate B

/-- `U ≥ 1`, the largest absolute value of an entry of `A` or `b` (paper: Section 3.1
(`sec:hom`)). The `max 1` only makes `U ≥ 1` hold by definition; for an admissible
LP, `A` has a nonzero integer entry, so the largest absolute value is `≥ 1`
anyway. -/
def U : ℕ :=
  max 1 (max (univ.sup fun ij : Fin m × Fin n ↦ (P.A ij.1 ij.2).natAbs)
             (univ.sup fun i : Fin m ↦ (P.b i).natAbs))

/-- `T = 2m(mU)^m + 1` (paper: Equation 4 (`eq:T`)). -/
def T : ℕ := 2 * m * (m * P.U) ^ m + 1

/-- `C = 1 + max_j |c_j|` (paper: Equation 6 (`eq:gamma`)). -/
def C : ℤ := 1 + ((univ.sup fun j : Fin n ↦ (P.c j).natAbs : ℕ) : ℤ)

/-- The costs `γ ∈ ℤ^{n+1}` of the induced LP (paper: Equation 6 (`eq:gamma`)):
`γ_j = C + c_j` for an original label `j`, and `γ_{n+1} = C` for the slack label. -/
def gamma : Fin (n + 1) → ℤ :=
  Fin.snoc (α := fun _ ↦ ℤ) (fun j ↦ P.C + P.c j) P.C

/-- The vectors `α_j ∈ ℝ^m` of the induced LP (paper: Equation 5 (`eq:alpha`)):
`α_j = A_j - b/T` for an original label `j`, and `α_{n+1} = -b/T` for the slack
label. -/
noncomputable def alpha : Fin (n + 1) → Fin m → ℝ :=
  Fin.snoc (α := fun _ ↦ Fin m → ℝ)
    (fun j i ↦ (P.A i j : ℝ) - (P.b i : ℝ) / P.T)
    (fun i ↦ -(P.b i : ℝ) / P.T)

/-- The induced linear program (LP_λ) in standard form (paper: `eq:induced-lp` and
the sentence after Equation 6 (`eq:gamma`)):
`min γᵀλ subject to Mλ = (0, 1)ᵀ, λ ≥ 0`, where the column `M_j = (α_j, 1)ᵀ`
(the `m` rows of `∑_j λ_j α_j = 0` first, then the row `∑_j λ_j = 1`; note that,
in contrast, the atoms below put their extra (cost) coordinate first). Not used in
the statements of `MainResults`, only in the proofs. -/
noncomputable def inducedLP : LP (m + 1) (n + 1) where
  A := Matrix.of fun i j ↦ Fin.snoc (α := fun _ ↦ ℝ) (P.alpha j) 1 i
  b := Fin.snoc (α := fun _ ↦ ℝ) 0 1
  c := fun j ↦ (P.gamma j : ℝ)

/-- The integer vectors `T α_j` (paper: first sentence of Section 3.2 (`sec:atoms`)):
`T A_j - b` for an original label `j`, and `-b` for the slack label. -/
def scaledAlpha : Fin (n + 1) → Fin m → ℤ :=
  Fin.snoc (α := fun _ ↦ Fin m → ℤ)
    (fun j i ↦ (P.T : ℤ) * P.A i j - P.b i)
    (fun i ↦ -P.b i)

/-- `K ≥ 1`, the largest absolute value of an entry of the integer vectors
`(γ_j, T α_j, 1)ᵀ`, `j ∈ [n+1]` (paper: Step 3, before Equation 17 (`eq:scale`)). -/
def K : ℕ :=
  univ.sup fun j : Fin (n + 1) ↦
    max (P.gamma j).natAbs (max (univ.sup fun i : Fin m ↦ (P.scaledAlpha j i).natAbs) 1)

/-- `H = ((m+1) K²)^{m+1}` (paper: Equation 17 (`eq:scale`)). -/
def H : ℕ := ((m + 1) * P.K ^ 2) ^ (m + 1)

/-- The scale factor `N = 2mTH³` (paper: Equation 17 (`eq:scale`)). -/
def N : ℕ := 2 * m * P.T * P.H ^ 3

/-- The atoms `p_j = (N γ_j, N² α_j)ᵀ ∈ ℝ^{m+1}`, `j ∈ [n+1]` (paper: Equation 12 (`eq:atoms`)).
Coordinate `0` is the cost coordinate `N γ_j`; coordinate `i+1` is `N² (α_j)_i`. -/
noncomputable def atom : Fin (n + 1) → Fin (m + 1) → ℝ :=
  fun j ↦ Fin.cons (α := fun _ ↦ ℝ) ((P.N : ℝ) * P.gamma j) (fun i ↦ (P.N : ℝ) ^ 2 * P.alpha j i)

/-- The largest absolute value of an entry of `A`, `b`, or `c`, but at least `2`.
Only used to state the size bound for the atoms. -/
def maxEntry : ℕ :=
  max 2 (max (max (univ.sup fun ij : Fin m × Fin n ↦ (P.A ij.1 ij.2).natAbs)
                  (univ.sup fun i : Fin m ↦ (P.b i).natAbs))
             (univ.sup fun j : Fin n ↦ (P.c j).natAbs))

end IntLP

/-- `B̂ = B ∪ {n+1}` for a label set `B ⊆ [n]` (paper: before Lemma 2 (`lem:hom`)):
the labels of `B`, read as labels of the induced LP, together with the slack label
`Fin.last n`. -/
def hat {n : ℕ} (B : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  insert (Fin.last n) (B.map Fin.castSuccEmb)

end WolfeSimplex
