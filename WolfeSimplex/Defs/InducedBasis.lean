import WolfeSimplex.Defs.Induced

/-!
# Basis quantities of the induced LP (paper: table after Equation 6 (`eq:gamma`), Equation 15
(`eq:projection-quantities`))

Trusted definitions of the quantities of a basis `S` of the induced LP (LP_λ)
(`P.inducedLP`, standard form `min γᵀλ, Mλ = (0, 1)ᵀ, λ ≥ 0`), in the paper's notation:

* `λ^S` is `P.inducedLP.basicSol S`, `d^{S,j}` is `P.inducedLP.basicDir S j`, and the
  reduced cost `γ̄^S_j` is `P.inducedLP.reducedCost S j` (all from `Defs/Simplex.lean`).
* The dual vector `(v^S, h^S)ᵀ = M_S^{-T} γ_S` (Equation 8 (`eq:nf-dual`)) is
  `P.inducedLP.dualVec S : Fin (m+1) → ℝ`; its first `m` entries are `v^S` (`vS`) and
  its last entry is `h^S` (`hS`), matching the rows of `M` (the `m` rows of
  `∑ λ_j α_j = 0` first, then the row `∑ λ_j = 1`).
* `u^S = M_S^{-1}(v^S, 0)ᵀ`, `ε^S = h^S/(N² + ‖v^S‖²)`, `s^S = N² ε^S`
  (Equation 15 (`eq:projection-quantities`)). As in `Defs/Simplex.lean`, `u^S` is defined by its
  characterizing property (`Mu = (v^S, 0)ᵀ`, `u` vanishes outside `S`).
-/

namespace WolfeSimplex

namespace IntLP

open Finset Matrix

variable {m n : ℕ} (P : IntLP m n)

/-- `v^S ∈ ℝ^m`, the first `m` entries of the dual vector of the basis `S` of (LP_λ)
(paper: Equation 8 (`eq:nf-dual`)). -/
noncomputable def vS (S : Finset (Fin (n + 1))) : Fin m → ℝ :=
  fun i ↦ P.inducedLP.dualVec S (Fin.castSucc i)

/-- `h^S ∈ ℝ`, the last entry of the dual vector of the basis `S` of (LP_λ)
(paper: Equation 8 (`eq:nf-dual`)). -/
noncomputable def hS (S : Finset (Fin (n + 1))) : ℝ :=
  P.inducedLP.dualVec S (Fin.last m)

/-- The defining property of `u^S = M_S^{-1}(v^S, 0)ᵀ`: `M u = (v^S, 0)ᵀ` and `u`
vanishes outside `S`. -/
def IsUSOf (S : Finset (Fin (n + 1))) (u : Fin (n + 1) → ℝ) : Prop :=
  P.inducedLP.A *ᵥ u = Fin.snoc (α := fun _ ↦ ℝ) (P.vS S) 0 ∧ ∀ k ∉ S, u k = 0

/-- `u^S = M_S^{-1}(v^S, 0)ᵀ` (paper: Equation 15 (`eq:projection-quantities`)). -/
noncomputable def uS (S : Finset (Fin (n + 1))) : Fin (n + 1) → ℝ :=
  Classical.epsilon (P.IsUSOf S)

/-- `ε^S = h^S / (N² + ‖v^S‖²)` (paper: Equation 15 (`eq:projection-quantities`)). -/
noncomputable def epsS (S : Finset (Fin (n + 1))) : ℝ :=
  P.hS S / ((P.N : ℝ) ^ 2 + P.vS S ⬝ᵥ P.vS S)

/-- `s^S = N² ε^S` (paper: Equation 15 (`eq:projection-quantities`)). -/
noncomputable def sS (S : Finset (Fin (n + 1))) : ℝ := (P.N : ℝ) ^ 2 * P.epsS S

end IntLP

end WolfeSimplex
