import WolfeSimplex.Defs.Induced
import WolfeSimplex.Defs.Rules

/-!
# The canonical LP, the shield, and the weighted shield (paper: Appendix C.2 (`app:cor-rules`)
(shortest-atom construction))

Trusted definitions for Appendix C.2 (`app:cor-rules`) (shortest-atom construction) ("Starting at
the
minimum-norm atom"):
the canonical LP with respect to a basis `B₀`, the LP (LP⁺) with the shield
(Equation 24 (`eq:shield`)), and the weighted LP (LP̃⁺) (Equation 35 (`eq:weights`)).

## Conventions

* The basis `B₀` is given by an *enumeration* `e : Fin m → Fin n` of its labels:
  `B₀ = {e 0, …, e (m-1)}` (`basisOf e`). The paper indexes the rows of the
  canonical LP by the labels of `B₀`; here row `i` belongs to the label `e i`.
* `A_{B₀}` is the square matrix with the columns `A_{e 0}, …, A_{e (m-1)}`
  (`basisMat`), and `Δ₀ = |det A_{B₀}|` (`Delta0`).
* The paper defines `A' = Δ₀ A_{B₀}⁻¹ A` and says that `Δ₀ A_{B₀}⁻¹` is the adjugate
  of `A_{B₀}` up to sign. Here, to stay with integers, we *define*
  `G = sign(det A_{B₀}) · adj(A_{B₀})` (which equals `Δ₀ A_{B₀}⁻¹` when `A_{B₀}` is
  nonsingular, since `adj(M) = det(M) M⁻¹`) and `A' = G A`, `b' = 2 G b`,
  `c' = Δ₀ c - A'ᵀ c_{B₀}`. The last formula is the paper's
  `c' = Δ₀ (c - Aᵀ y^{B₀})`, because `Δ₀ y^{B₀} = Gᵀ c_{B₀}`.
* (LP⁺) has the labels `Fin (n+1)`: the original labels `Fin.castSucc k` and the
  shield `ω = Fin.last n`. Its rows are `Fin (m+1)`: row `Fin.castSucc i` is row `i`
  of the canonical LP, and row `Fin.last m` is the shield row (Equation 24 (`eq:shield`)).
  So, for a label set `B ⊆ [n]`, the set `B ∪ {ω}` is `hat B` (`Defs/Induced.lean`).
* The atoms of (LP⁺) (Equation 31 (`eq:shield-atoms`)) are `(P.shieldLP e).atom`, with labels
  `Fin (n+2)`: the original label `k` is `k.castSucc.castSucc`, the shield `ω` is
  `(Fin.last n).castSucc`, and the slack label (the paper's `n+2`) is
  `Fin.last (n+1)`. The corral of the basis `B ∪ {ω}` is `hat (hat B)`.
-/

namespace WolfeSimplex

open Finset Matrix

/-- The label set `{e 0, …, e (m-1)}` enumerated by `e`. -/
def basisOf {m n : ℕ} (e : Fin m → Fin n) : Finset (Fin n) := univ.image e

namespace IntLP

variable {m n : ℕ} (P : IntLP m n) (e : Fin m → Fin n)

/-- The square matrix `A_{B₀}` with the columns `A_{e 0}, …, A_{e (m-1)}`. -/
def basisMat : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun i k ↦ P.A i (e k)

/-- `Δ₀ = |det A_{B₀}|` (paper: Appendix C.2 (`app:cor-rules`) (shortest-atom construction)). -/
def Delta0 : ℤ := |(P.basisMat e).det|

/-- `G = sign(det A_{B₀}) · adj(A_{B₀})`, which is `Δ₀ A_{B₀}⁻¹` for a basis `B₀`. -/
def canonG : Matrix (Fin m) (Fin m) ℤ := (P.basisMat e).det.sign • (P.basisMat e).adjugate

/-- The canonical LP with respect to `B₀` (paper: Appendix C.2 (`app:cor-rules`) (shortest-atom
construction)), scaled to
integer data: `A' = Δ₀ A_{B₀}⁻¹ A`, `b' = 2 Δ₀ A_{B₀}⁻¹ b`,
`c' = Δ₀ (c - Aᵀ y^{B₀})`, written with the integer matrix `G = Δ₀ A_{B₀}⁻¹`
(see the conventions above). -/
def canonical : IntLP m n where
  A := P.canonG e * P.A
  b := fun i ↦ 2 * (P.canonG e *ᵥ P.b) i
  c := fun j ↦ P.Delta0 e * P.c j - ∑ i, (P.canonG e * P.A) i j * P.c (e i)

/-- The coefficient `a = Δ₀ + max_{k ∈ [n] \ B₀} ∑_{i ∈ B₀} b'_i max{A'_{ik}, 0}`
of the shield constraint (paper: Equation 24 (`eq:shield`)). (Each sum is a nonnegative integer
when `B₀` is a feasible nondegenerate basis; `toNat` only makes the maximum a
natural number. The maximum over the empty set is `0`.) -/
def shieldCoeff : ℤ :=
  P.Delta0 e + (((univ.filter fun k ↦ k ∉ basisOf e).sup fun k ↦
    (∑ i, (P.canonical e).b i * max ((P.canonical e).A i k) 0).toNat : ℕ) : ℤ)

/-- The LP (LP⁺) of Appendix C.2 (`app:cor-rules`) (shortest-atom construction): the canonical LP
with the new variable
`x_ω` (the shield, label `Fin.last n`, cost `0`, column `0` in the old rows) and the
new constraint `Δ₀ x_ω - a ∑_{k ∈ [n] \ B₀} x_k = 1` (paper: Equation 24 (`eq:shield`)) as the last
row `Fin.last m`. So `b⁺ = (b', 1)` and `c⁺ = (c', 0)`. -/
def shieldLP : IntLP (m + 1) (n + 1) where
  A := Matrix.of fun r k ↦
    Fin.snoc (α := fun _ ↦ Fin (n + 1) → ℤ)
      (fun i ↦ Fin.snoc (α := fun _ ↦ ℤ) (fun k' ↦ (P.canonical e).A i k') 0)
      (Fin.snoc (α := fun _ ↦ ℤ) (fun k' ↦ if k' ∈ basisOf e then 0 else -P.shieldCoeff e)
        (P.Delta0 e))
      r k
  b := Fin.snoc (α := fun _ ↦ ℤ) (P.canonical e).b 1
  c := Fin.snoc (α := fun _ ↦ ℤ) (P.canonical e).c 0

/-- The number `W = a + max_{k ∈ [n] \ B₀} ‖A'_k‖²` (paper: before Equation 35 (`eq:weights`)). -/
def shieldW : ℤ :=
  P.shieldCoeff e + (((univ.filter fun k ↦ k ∉ basisOf e).sup fun k ↦
    (∑ i, (P.canonical e).A i k ^ 2).toNat : ℕ) : ℤ)

/-- The position `r(ℓ)` of a label of (LP⁺) for the order `≺` of `[n]` given by the
permutation `σ` (the label `k` is at position `σ k + 1`), and `r(ω) = n + 1`
(paper: before Equation 35 (`eq:weights`)). -/
def shieldRank {n : ℕ} (σ : Equiv.Perm (Fin n)) : Fin (n + 1) → ℕ :=
  Fin.snoc (α := fun _ ↦ ℕ) (fun k ↦ (σ k : ℕ) + 1) (n + 1)

/-- The weighted LP (LP̃⁺) of Appendix C.2 (`app:cor-rules`) (shortest-atom construction) for the
order given by `σ`
(paper: Equation 35 (`eq:weights`)): it arises from (LP⁺) by replacing the column `Δ₀ e_ℓ` of every
`ℓ ∈ B₀ ∪ {ω}` by `d_ℓ e_ℓ` with `d_ℓ = r(ℓ) W`, and the coefficient `-a` of every
`x_k`, `k ∈ [n] \ B₀`, in the shield row by `-a_k` with `a_k = r(k) W`. Right-hand
side and costs are those of (LP⁺). Explicitly, the column of `ℓ = e i ∈ B₀` has the
single nonzero entry `d_ℓ` in row `i`. -/
def weightedLP (σ : Equiv.Perm (Fin n)) : IntLP (m + 1) (n + 1) where
  A := Matrix.of fun r k ↦
    Fin.snoc (α := fun _ ↦ Fin (n + 1) → ℤ)
      (fun i ↦ Fin.snoc (α := fun _ ↦ ℤ)
        (fun k' ↦ if k' ∈ basisOf e then
            (if e i = k' then (shieldRank σ (Fin.castSucc k') : ℤ) * P.shieldW e else 0)
          else (P.canonical e).A i k') 0)
      (Fin.snoc (α := fun _ ↦ ℤ)
        (fun k' ↦ if k' ∈ basisOf e then 0
          else -((shieldRank σ (Fin.castSucc k') : ℤ) * P.shieldW e))
        ((shieldRank σ (Fin.last n) : ℤ) * P.shieldW e))
      r k
  b := (P.shieldLP e).b
  c := (P.shieldLP e).c

end IntLP

end WolfeSimplex
