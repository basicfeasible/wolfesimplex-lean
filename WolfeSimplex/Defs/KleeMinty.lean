import WolfeSimplex.Defs.Induced

/-!
# The Klee–Minty cube (paper: Equation 34 (`eq:km`))

Trusted definition of the Klee–Minty LP Equation 34 (`eq:km`) in Chvátal's integer form:
`min -∑_j 10^{n-j} x_j` subject to `x_i + s_i + 2 ∑_{j<i} 10^{i-j} x_j = 100^{i-1}`
for `i ∈ [n]`, and `x, s ≥ 0`.

## Conventions

* Pairs and rows are numbered `0, …, n-1` (the paper: `1, …, n`). With this
  shift, row `i` reads `x_i + s_i + 2 ∑_{j<i} 10^{i-j} x_j = 100^i`, and the cost
  of `x_j` is `-10^{n-1-j}`.
* The `2n` labels are `Fin (2n)`: `x_j` is the label `2j` and `s_i` is the label
  `2i+1`. So the natural order of `Fin (2n)` is the order
  `x_1 ≺ s_1 ≺ x_2 ≺ s_2 ≺ … ≺ x_n ≺ s_n` of Lemma 15 (`lem:km`).
-/

namespace WolfeSimplex

/-- The Klee–Minty LP Equation 34 (`eq:km`) with `n` rows and the `2n` labels
`x_j = 2j`, `s_i = 2i+1`. -/
def kleeMinty (n : ℕ) : IntLP n (2 * n) where
  A := Matrix.of fun i k ↦
    if k.val % 2 = 1 then
      (if k.val / 2 = i.val then 1 else 0)          -- the column of `s_{k/2}`
    else if k.val / 2 = i.val then 1                -- the column of `x_{k/2}`
    else if k.val / 2 < i.val then 2 * 10 ^ (i.val - k.val / 2)
    else 0
  b := fun i ↦ 100 ^ i.val
  c := fun k ↦ if k.val % 2 = 0 then -(10 ^ (n - 1 - k.val / 2)) else 0

/-- The label `s_i = 2i+1` of the slack variable of row `i`. The initial basis of
Lemma 15 (`lem:km`) is `B₀ = {s_1, …, s_n} = basisOf (kmSlack n)`. -/
def kmSlack (n : ℕ) : Fin n → Fin (2 * n) := fun i ↦ ⟨2 * i.val + 1, by omega⟩

end WolfeSimplex
