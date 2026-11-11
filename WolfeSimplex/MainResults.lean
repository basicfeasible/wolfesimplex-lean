import WolfeSimplex.Defs.Induced
import WolfeSimplex.Defs.Shield
import WolfeSimplex.Defs.KleeMinty
import WolfeSimplex.Defs.LawsonHanson
import WolfeSimplex.Defs.InducedBasis
import WolfeSimplex.Proofs.Pivot
import WolfeSimplex.Proofs.InitRuns
import WolfeSimplex.Proofs.Identities
import WolfeSimplex.Proofs.InducedLemmas
import WolfeSimplex.Proofs.AffineMin
import WolfeSimplex.Proofs.NNLS
import WolfeSimplex.Proofs.HistoryRuns
import WolfeSimplex.Proofs.RandomRuns
import WolfeSimplex.Proofs.Cap
import WolfeSimplex.Proofs.Scaling

/-!
# Main results

Catalog of the main results of the paper. For Theorem 1 alone, the shorter review
entry point is `PaperTheorem1.lean`, with only `Defs/Simplex`, `Defs/Wolfe` and
`Defs/Induced`. This catalog is useful for reviewing the additional results.
Definitions and theorem statements must still be interpreted against the paper.

Theorem 1 (`thm:equivalence`) of the paper is split into the parts
`equivalence_integral`, `equivalence_size` (the construction and its size),
and `equivalence_a` … `equivalence_d` (parts (a)–(d)).

Each statement is proved by a reference to the proof files in `WolfeSimplex/Proofs/`.
-/

namespace WolfeSimplex

open Finset Wolfe

variable {m n : ℕ}

/-! ## Section 2 (`sec:prelim`) -/

/-- Lemma 7 (`lem:identities`): let `B` be a basis and `j` a label. (a) every basic label
has reduced cost `0`; (b) the basic solution `x^B` is the unique `x` with `Ax = b` and
`x_k = 0` for `k ∉ B`, and `z_B = (y^B)ᵀ b`; (c) if `j` is nonbasic, the basic direction
`d^{B,j}` is the unique `d` with `Ad = 0`, `d_j = 1`, `d_k = 0` for `k ∉ B ∪ {j}`, and
`cᵀ d^{B,j} = c̄^B_j`. -/
theorem identities (P : LP m n) (B : Finset (Fin n)) (hB : P.IsBasis B) (j : Fin n) :
    (∀ i ∈ B, P.reducedCost B i = 0) ∧
    ((∀ x, P.IsBasicSolutionOf B x ↔ x = P.basicSol B) ∧
      P.objValue B = P.dualVec B ⬝ᵥ P.b) ∧
    (j ∉ B → (∀ d, P.IsBasicDirOf B j d ↔ d = P.basicDir B j) ∧
      P.c ⬝ᵥ P.basicDir B j = P.reducedCost B j) :=
  P.identities_main B hB j

/-- Lemma 1 (`lem:affine-min`), together with the well-definedness of `w_S` and `λ^{*S}`
(Section 2.2 (`sec:wolfe`)): for an affinely independent support `S`, the affine minimizer
`w_S` and its coefficients `λ^{*S}` exist and are unique; (a) a point `w ∈ aff(S)`
equals `w_S` iff `g_i(w) = 0` for all `i ∈ S`; (b) if `g_j(w_S) ≠ 0`, then `S ∪ {j}` is
affinely independent; (c) if `S` is a corral, then `w_S` is the optimal solution of
(MNP) iff `Γ(w_S) = ∅`. -/
theorem affine_min {N D : ℕ} (p : Fin N → Fin D → ℝ) (S : Finset (Fin N)) (hS : S.Nonempty)
    (hAI : IsAffinelyIndependent p S) :
    (IsAffineMinimizerOf p S (affineMin p S) ∧
      (∀ x, IsAffineMinimizerOf p S x → x = affineMin p S) ∧
      IsAffineCoeffsOf p S (affineCoeffs p S) ∧
      (∀ lam, IsAffineCoeffsOf p S lam → lam = affineCoeffs p S)) ∧
    (∀ w ∈ affineHull p S, w = affineMin p S ↔ ∀ i ∈ S, gap p i w = 0) ∧
    (∀ j, gap p j (affineMin p S) ≠ 0 → IsAffinelyIndependent p (insert j S)) ∧
    (IsCorral p S → (IsMinNormPoint p (affineMin p S) ↔ improving p (affineMin p S) = ∅)) :=
  affine_min_main p S hS hAI

/-- Well-definedness and termination of Wolfe's method (Section 2.2 (`sec:wolfe`) and
the termination discussion in Section 2.2 (`sec:wolfe`)): every singleton is a corral;
at a corral `S`, a major cycle that inserts any improving `j` can be carried out to the
end (the minor cycles always reach a corral); whichever zero-coefficient label each
minor cycle deletes, the support stays affinely independent, the coefficients stay
nonnegative, and a minor cycle is possible as long as the support is not a corral (so
no choice gets stuck); every chain of minor cycles in it has
at most `D` steps; every major cycle strictly decreases the norm of the affine
minimizer; hence no corral occurs twice in a (partial) run, and every partial run,
with any insertion rule, has fewer than `2^N` major cycles, so the method always stops. -/
theorem wolfe_well_defined {N D : ℕ} (p : Fin N → Fin D → ℝ) :
    (∀ k, IsCorral p {k}) ∧
    (∀ S j, IsCorral p S → j ∈ improving p (affineMin p S) → ∃ S', MajorCycle p S j S') ∧
    (∀ S j s, IsCorral p S → j ∈ improving p (affineMin p S) →
      Relation.ReflTransGen (MinorCycle p) ⟨insert j S, affineCoeffs p S⟩ s →
      IsAffinelyIndependent p s.S ∧ (∀ k, 0 ≤ s.lam k) ∧
      (¬ IsCorral p s.S → ∃ s', MinorCycle p s s')) ∧
    (∀ S j (k : ℕ) (s : ℕ → Wolfe.State N), IsCorral p S → j ∈ improving p (affineMin p S) →
      s 0 = ⟨insert j S, affineCoeffs p S⟩ → (∀ t < k, MinorCycle p (s t) (s (t + 1))) →
      k ≤ D) ∧
    (∀ S j S', MajorCycle p S j S' → normSq (affineMin p S') < normSq (affineMin p S)) ∧
    ∀ (ch : Finset (Fin N) → Fin N → Prop) f S, IsPartialWolfeRunWith p ch f S →
      Set.InjOn S (Set.Iic f) ∧ f < 2 ^ N :=
  wolfe_well_defined_main p

/-! ## Section 3 (`sec:equivalence`) -/

/-- Theorem 1 (`thm:equivalence`), construction: the atoms `p_1, …, p_{n+1}` of
Equation 12 (`eq:atoms`) are integer vectors. -/
theorem equivalence_integral (P : IntLP m n) (hP : P.IsAdmissible) :
    ∀ j k, ∃ z : ℤ, P.atom j k = z :=
  P.atom_integral

/-- Theorem 1 (`thm:equivalence`), construction (size, replaces "polynomial time"; cf.
Lemma 10 (`lem:encoding`)): with `W = max(2, largest absolute value of an entry of
A, b, c)`, every coordinate of every atom has absolute value at most
`((m+1) W)^{36 (m+1)²}`. Hence every coordinate has bit length
`O(m² log((m+1) W))`, polynomial in the bit length of `(A, b, c)`. -/
theorem equivalence_size (P : IntLP m n) (hP : P.IsAdmissible) :
    ∀ j k, |P.atom j k| ≤ (((m + 1) * P.maxEntry : ℕ) : ℝ) ^ (36 * (m + 1) ^ 2) :=
  P.atom_size hP.1

/-- Theorem 1 (`thm:equivalence`)(a): for every feasible basis `B`, the set
`B̂ = B ∪ {n+1}` is a corral, the improving atoms at its affine minimizer `w_B̂`
are exactly the improving labels at `B`, and there is `κ > 0` with
`g_j(w_B̂) = κ c̄^B_j` for `j ∈ [n]` and `g_{n+1}(w_B̂) = 0`. -/
theorem equivalence_a (P : IntLP m n) (hP : P.IsAdmissible)
    (B : Finset (Fin n)) (hB : P.toLP.IsFeasibleBasis B) :
    IsCorral P.atom (hat B) ∧
    improving P.atom (affineMin P.atom (hat B)) = (P.toLP.improving B).map Fin.castSuccEmb ∧
    ∃ κ : ℝ, 0 < κ ∧
      (∀ j : Fin n, gap P.atom (Fin.castSucc j) (affineMin P.atom (hat B)) =
        κ * P.toLP.reducedCost B j) ∧
      gap P.atom (Fin.last n) (affineMin P.atom (hat B)) = 0 :=
  IntLP.thm_a hP hB

/-- Theorem 1 (`thm:equivalence`)(b): let `B` be a feasible basis, `j ∈ Γ(B)`, and let
`B' = (B \ {i*}) ∪ {j}` be the pivot on `j` with leaving label `i*`. The major
cycle that inserts `p_j` at the corral `B̂` consists of exactly one minor cycle,
which deletes exactly `i*`, and an acceptance; the next corral is `B̂'`.

In detail: the support `B̂ ∪ {j}` after the insertion is not a corral (so at least
one minor cycle happens); a minor cycle from the state after the insertion exists,
and every such minor cycle results in the support `B̂'` (= `B̂ ∪ {j}` minus `i*`);
`B̂'` is a corral (so no further minor cycle happens); and the major cycles at `B̂`
that insert `j` are exactly those that end at `B̂'`. -/
theorem equivalence_b (P : IntLP m n) (hP : P.IsAdmissible)
    (B : Finset (Fin n)) (hB : P.toLP.IsFeasibleBasis B)
    (j : Fin n) (hj : j ∈ P.toLP.improving B) (i : Fin n) (hi : P.toLP.IsLeavingLabel B j i) :
    ¬ IsCorral P.atom (insert (Fin.castSucc j) (hat B)) ∧
    (∃ s', MinorCycle P.atom ⟨insert (Fin.castSucc j) (hat B), affineCoeffs P.atom (hat B)⟩ s') ∧
    (∀ s', MinorCycle P.atom ⟨insert (Fin.castSucc j) (hat B), affineCoeffs P.atom (hat B)⟩ s' →
      s'.S = hat (insert j (B.erase i))) ∧
    IsCorral P.atom (hat (insert j (B.erase i))) ∧
    ∀ S' : Finset (Fin (n + 1)),
      MajorCycle P.atom (hat B) (Fin.castSucc j) S' ↔ S' = hat (insert j (B.erase i)) :=
  IntLP.thm_b hP hB hj hi

/-- Theorem 1 (`thm:equivalence`)(c): let `B₀` be a feasible basis. The Wolfe runs
from `B̂₀` are exactly the sequences `B̂₀, …, B̂_f` for the simplex runs
`B₀, …, B_f` from `B₀`. -/
theorem equivalence_c (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀)
    (f : ℕ) (S : ℕ → Finset (Fin (n + 1))) :
    (IsWolfeRun P.atom f S ∧ S 0 = hat B₀) ↔
      ∃ B : ℕ → Finset (Fin n), P.toLP.IsSimplexRun f B ∧ B 0 = B₀ ∧
        ∀ k ≤ f, S k = hat (B k) :=
  IntLP.thm_c hP B₀ hB₀ f S

/-- Theorem 1 (`thm:equivalence`)(d): for every feasible basis `B`, Wolfe's method stops
at `B̂` (no improving atom at `w_B̂`) with the optimal solution `w_B̂` of the
minimum-norm-point problem on the atoms if and only if `B` is optimal. -/
theorem equivalence_d (P : IntLP m n) (hP : P.IsAdmissible)
    (B : Finset (Fin n)) (hB : P.toLP.IsFeasibleBasis B) :
    (improving P.atom (affineMin P.atom (hat B)) = ∅ ∧
      IsMinNormPoint P.atom (affineMin P.atom (hat B))) ↔ P.toLP.IsOptimalBasis B :=
  IntLP.thm_d hP hB

/-! ## The lemmas of Section 3 (`sec:equivalence`) and Appendix B.1 (`app:statements`)

Notation: `L = P.inducedLP` is (LP_λ) in standard form; `λ^S = L.basicSol S`,
`d^{S,j} = L.basicDir S j`, `γ̄^S_j = L.reducedCost S j`, `(v^S, h^S) = (P.vS S, P.hS S)`,
`u^S, ε^S, s^S = P.uS S, P.epsS S, P.sS S` (`Defs/InducedBasis.lean`). -/

/-- Lemma 8 (`lem:T-bound`): every feasible point `x` of an admissible LP satisfies
`2 · 1ᵀx < T`. -/
theorem T_bound (P : IntLP m n) (hP : P.IsAdmissible) (x : Fin n → ℝ)
    (hx : P.toLP.IsFeasible x) : 2 * ∑ j, x j < P.T :=
  T_bound_main P hP x hx

/-- Lemma 9 (`lem:induced-facts`): for a basis `S` of (LP_λ) and a label `j`:
(a) `∑_{i∈S} λ^S_i α_i = 0` and `∑_{i∈S} λ^S_i = 1`; (b) `γᵀλ^S = h^S`, and `h^S ≥ 1`
if `S` is feasible; (c) if `j ∉ S`, then `∑_k d^{S,j}_k α_k = 0`, `∑_k d^{S,j}_k = 0`,
and `γᵀ d^{S,j} = γ̄^S_j`. -/
theorem induced_facts (P : IntLP m n) (S : Finset (Fin (n + 1))) (hS : P.inducedLP.IsBasis S)
    (j : Fin (n + 1)) :
    (∑ i ∈ S, P.inducedLP.basicSol S i • P.alpha i = 0 ∧
      ∑ i ∈ S, P.inducedLP.basicSol S i = 1) ∧
    (∑ i, (P.gamma i : ℝ) * P.inducedLP.basicSol S i = P.hS S ∧
      (P.inducedLP.IsFeasibleBasis S → 1 ≤ P.hS S)) ∧
    (j ∉ S → ∑ k, P.inducedLP.basicDir S j k • P.alpha k = 0 ∧
      ∑ k, P.inducedLP.basicDir S j k = 0 ∧
      ∑ k, (P.gamma k : ℝ) * P.inducedLP.basicDir S j k = P.inducedLP.reducedCost S j) :=
  induced_facts_main P S hS j

/-- Lemma 10 (`lem:encoding`): the atoms are integer vectors, and the numbers `T, C, K, H, N`
and the entries of the atoms have absolute value at most `((m+1) W)^{36 (m+1)²}`
(`W = P.maxEntry`), i.e. bit length polynomial in that of `(A, b, c)`. (The running
time of the construction is not formalized.) -/
theorem encoding (P : IntLP m n) (hP : P.IsAdmissible) :
    (∀ j k, ∃ z : ℤ, P.atom j k = z) ∧
    P.T ≤ ((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) ∧
    P.C ≤ ((((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) : ℕ) : ℤ) ∧
    P.K ≤ ((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) ∧
    P.H ≤ ((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) ∧
    P.N ≤ ((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) ∧
    ∀ j k, |P.atom j k| ≤ (((m + 1) * P.maxEntry : ℕ) : ℝ) ^ (36 * (m + 1) ^ 2) :=
  encoding_main P hP

/-- Lemma 2 (`lem:hom`): (LP_λ) has a constraint matrix of full row rank, a nonempty
bounded feasible set, and only nondegenerate feasible bases; `B ↦ B̂` is a bijection
from the feasible bases of (LP) onto those of (LP_λ); every feasible basis `B`
satisfies (a) `λ^{B̂} = (x^B, T − 1ᵀx^B)ᵀ/T`, (b) `(v^{B̂}, h^{B̂}) = (y^B, C + z_B/T)`,
(c) `γ̄^{B̂}_j = c̄^B_j` for `j ∈ [n]` and `γ̄^{B̂}_{n+1} = 0`; for every `j ∈ Γ(B)`, the
pivots on `j` at `B` and at `B̂` have the same unique leaving label; hence the pivots
correspond, and `B_0, …, B_f` is a simplex run on (LP) iff `B̂_0, …, B̂_f` is one on
(LP_λ). -/
theorem hom (P : IntLP m n) (hP : P.IsAdmissible) :
    (P.inducedLP.A.rank = m + 1 ∧ P.inducedLP.FeasibleSetNonemptyBounded ∧
      ∀ S, P.inducedLP.IsFeasibleBasis S → P.inducedLP.IsNondegenerate S) ∧
    (∀ S, P.inducedLP.IsFeasibleBasis S ↔ ∃ B, P.toLP.IsFeasibleBasis B ∧ S = hat B) ∧
    (∀ B, P.toLP.IsFeasibleBasis B →
      P.inducedLP.basicSol (hat B) =
        Fin.snoc (α := fun _ ↦ ℝ) (fun k ↦ P.toLP.basicSol B k / P.T)
          ((P.T - ∑ k, P.toLP.basicSol B k) / P.T) ∧
      (P.vS (hat B) = P.toLP.dualVec B ∧ P.hS (hat B) = P.C + P.toLP.objValue B / P.T) ∧
      (∀ j : Fin n, P.inducedLP.reducedCost (hat B) (Fin.castSucc j) = P.toLP.reducedCost B j) ∧
      P.inducedLP.reducedCost (hat B) (Fin.last n) = 0) ∧
    (∀ B, P.toLP.IsFeasibleBasis B → ∀ j ∈ P.toLP.improving B,
      (∃! i, P.toLP.IsLeavingLabel B j i) ∧
      ∀ i' : Fin (n + 1), P.inducedLP.IsLeavingLabel (hat B) (Fin.castSucc j) i' ↔
        ∃ i, i' = Fin.castSucc i ∧ P.toLP.IsLeavingLabel B j i) ∧
    (∀ B j B', P.toLP.IsFeasibleBasis B →
      (P.toLP.IsPivot B j B' ↔ P.inducedLP.IsPivot (hat B) (Fin.castSucc j) (hat B'))) ∧
    ∀ f (B : ℕ → Finset (Fin n)),
      P.toLP.IsSimplexRun f B ↔ P.inducedLP.IsSimplexRun f (fun k ↦ hat (B k)) :=
  hom_main P hP

/-- Lemma 3 (`lem:direction`): for a basis `S` of (LP_λ), `j ∉ S`, and every `w`,
`p_j + ∑_{i∈S} d^{S,j}_i p_i = N γ̄^S_j e_1` and
`g_j(w) + ∑_{i∈S} d^{S,j}_i g_i(w) = N γ̄^S_j w_1` (`e_1`, `w_1`: the cost coordinate,
which is coordinate `0` here). -/
theorem direction (P : IntLP m n) (S : Finset (Fin (n + 1))) (hS : P.inducedLP.IsBasis S)
    (j : Fin (n + 1)) (hj : j ∉ S) (w : Fin (m + 1) → ℝ) :
    P.atom j + ∑ i ∈ S, P.inducedLP.basicDir S j i • P.atom i =
      ((P.N : ℝ) * P.inducedLP.reducedCost S j) • Pi.single 0 1 ∧
    gap P.atom j w + ∑ i ∈ S, P.inducedLP.basicDir S j i * gap P.atom i w =
      (P.N : ℝ) * P.inducedLP.reducedCost S j * w 0 :=
  direction_main P S hS j hj w

/-- Lemma 4 (`lem:corral`): for a basis `S` of (LP_λ): (a) the atoms of `S` are affinely
independent, `λ^{*S} = λ^S − ε^S u^S`, `w_S = (N s^S, −N² ε^S v^S)ᵀ`, and
`γᵀλ^{*S} = s^S = h^S − ε^S ‖v^S‖²`; (b) `g_j(w_S) = N² s^S γ̄^S_j` for every label `j`,
and `s^S > 0` if `S` is feasible. -/
theorem corral (P : IntLP m n) (hP : P.IsAdmissible) (S : Finset (Fin (n + 1)))
    (hS : P.inducedLP.IsBasis S) :
    (IsAffinelyIndependent P.atom S ∧
      affineCoeffs P.atom S = P.inducedLP.basicSol S - P.epsS S • P.uS S ∧
      affineMin P.atom S = Fin.cons (α := fun _ ↦ ℝ) ((P.N : ℝ) * P.sS S)
        (fun i ↦ -(P.N : ℝ) ^ 2 * P.epsS S * P.vS S i) ∧
      ∑ i, (P.gamma i : ℝ) * affineCoeffs P.atom S i = P.sS S ∧
      P.sS S = P.hS S - P.epsS S * (P.vS S ⬝ᵥ P.vS S)) ∧
    (∀ j, gap P.atom j (affineMin P.atom S) = (P.N : ℝ) ^ 2 * P.sS S * P.inducedLP.reducedCost S j) ∧
    (P.inducedLP.IsFeasibleBasis S → 0 < P.sS S) :=
  corral_main P hP S hS

/-- Lemma 5 (`lem:bases-corrals`): for a feasible basis `S` of (LP_λ): (a) `λ^S_i ≥ 1/H`
for `i ∈ S`; (b) for `j ∉ S`, every nonzero coordinate of `d^{S,j}` has absolute value
between `1/H` and `H`; (c) `|λ^{*S}_i − λ^S_i| = ε^S |u^S_i| ≤ 1/(4mH³)` for every `i`
(i.e. `‖λ^{*S} − λ^S‖_∞ = ε^S ‖u^S‖_∞ ≤ 1/(4mH³)`); in particular `S` is a corral. -/
theorem bases_corrals (P : IntLP m n) (hP : P.IsAdmissible) (S : Finset (Fin (n + 1)))
    (hS : P.inducedLP.IsFeasibleBasis S) :
    (∀ i ∈ S, 1 / (P.H : ℝ) ≤ P.inducedLP.basicSol S i) ∧
    (∀ j ∉ S, ∀ k, P.inducedLP.basicDir S j k ≠ 0 →
      1 / (P.H : ℝ) ≤ |P.inducedLP.basicDir S j k| ∧ |P.inducedLP.basicDir S j k| ≤ P.H) ∧
    (∀ i, |affineCoeffs P.atom S i - P.inducedLP.basicSol S i| = P.epsS S * |P.uS S i| ∧
      P.epsS S * |P.uS S i| ≤ 1 / (4 * m * (P.H : ℝ) ^ 3)) ∧
    IsCorral P.atom S :=
  bases_corrals_main P hP S hS

/-- Lemma 6 (`lem:pivot`): let `S` be a feasible basis of (LP_λ), `γ̄^S_j < 0`, and
`S' = (S \ {i*}) ∪ {j}` the pivot on `j` with leaving label `i*`. The major cycle that
inserts `p_j` at the corral `S` consists of exactly one minor cycle, which deletes
exactly `i*`, followed by acceptance; the next corral is `S'` (in detail as in
`equivalence_b`). -/
theorem pivot (P : IntLP m n) (hP : P.IsAdmissible) (S : Finset (Fin (n + 1)))
    (hS : P.inducedLP.IsFeasibleBasis S) (j : Fin (n + 1))
    (hj : P.inducedLP.reducedCost S j < 0) (i : Fin (n + 1))
    (hi : P.inducedLP.IsLeavingLabel S j i) :
    ¬ IsCorral P.atom (insert j S) ∧
    (∃ s', MinorCycle P.atom ⟨insert j S, affineCoeffs P.atom S⟩ s') ∧
    (∀ s', MinorCycle P.atom ⟨insert j S, affineCoeffs P.atom S⟩ s' →
      s'.S = insert j (S.erase i)) ∧
    IsCorral P.atom (insert j (S.erase i)) ∧
    ∀ S' : Finset (Fin (n + 1)), MajorCycle P.atom S j S' ↔ S' = insert j (S.erase i) :=
  pivot_main P hP S hS j hj i hi

/-! ## Corollary 2 (`cor:intro-rules`): insertion rules that are equivalent to pivot rules

The rule-correspondence argument in the proof of Lemma 11 (`lem:rules`): started at `B̂₀`,
every insertion rule of Table 1 (`tab:wolfe-rules`) produces the same runs as the corresponding
pivot rule started at `B₀`.
For the deterministic rules, ties are modeled as in `Defs/Rules.lean` (every tied label is
allowed), so "with the same tie-breaking" becomes: the possible runs (and, for the
history-dependent rules, the sequences of entered/inserted labels) correspond exactly.
For the randomized rules, the distributions of the runs agree (`Defs/RandomRules.lean`).
The external lower-bound constructions for the history-dependent and randomized simplex
rules are not formalized. The Klee–Minty bounds are proved below. -/

/-- Corollary 2 (`cor:intro-rules`), linopt / Dantzig: the Wolfe runs with linopt from `B̂₀` are
exactly the hats of the simplex runs with Dantzig's rule from `B₀`. -/
theorem rules_dantzig (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (f : ℕ)
    (S : ℕ → Finset (Fin (n + 1))) :
    (IsWolfeRunWith P.atom (IsLinoptChoice P.atom) f S ∧ S 0 = hat B₀) ↔
      ∃ B, P.toLP.IsSimplexRunWith P.toLP.IsDantzigChoice f B ∧ B 0 = B₀ ∧
        ∀ k ≤ f, S k = hat (B k) :=
  IntLP.rules_dantzig_main P hP B₀ hB₀ f S

/-- Corollary 2 (`cor:intro-rules`), least label / Bland: for an order of the labels `[n+1]` (rank
function `ρ`), the Wolfe runs with the least-label rule from `B̂₀` are exactly the hats of
the simplex runs with Bland's rule for the induced order of `[n]` from `B₀`. (For the natural
order, `ρ = Fin.val`, the induced order is the natural order of `[n]`.) -/
theorem rules_bland (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (ρ : Fin (n + 1) → ℕ) (f : ℕ)
    (S : ℕ → Finset (Fin (n + 1))) :
    (IsWolfeRunWith P.atom (IsLeastLabelChoice P.atom ρ) f S ∧ S 0 = hat B₀) ↔
      ∃ B, P.toLP.IsSimplexRunWith (P.toLP.IsBlandChoice fun k ↦ ρ (Fin.castSucc k)) f B ∧
        B 0 = B₀ ∧ ∀ k ≤ f, S k = hat (B k) :=
  IntLP.rules_bland_main P hP B₀ hB₀ ρ f S

/-- Corollary 2 (`cor:intro-rules`), least inserted / Zadeh: the Wolfe runs `S` with inserted labels
`J'` with the least-inserted rule from `B̂₀` are exactly the hats of the simplex runs `B`
with entering labels `J` with Zadeh's rule from `B₀`. -/
theorem rules_zadeh (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (f : ℕ)
    (S : ℕ → Finset (Fin (n + 1))) (J' : ℕ → Fin (n + 1)) :
    (IsWolfeRunWithHist P.atom (IsLeastInsertedChoice P.atom) f S J' ∧ S 0 = hat B₀) ↔
      ∃ B J, P.toLP.IsSimplexRunWithHist P.toLP.IsZadehChoice f B J ∧ B 0 = B₀ ∧
        (∀ k ≤ f, S k = hat (B k)) ∧ ∀ k < f, J' k = Fin.castSucc (J k) :=
  IntLP.rules_zadeh_main P hP B₀ hB₀ f S J'

/-- Corollary 2 (`cor:intro-rules`), round robin / Cunningham: as `rules_zadeh`, for the round-robin
rule (cyclic order of `[n+1]`, initial label `j₀`) and Cunningham's rule (cyclic order of
`[n]`, initial label `j₀`). -/
theorem rules_cunningham (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (j₀ : Fin n) (f : ℕ)
    (S : ℕ → Finset (Fin (n + 1))) (J' : ℕ → Fin (n + 1)) :
    (IsWolfeRunWithHist P.atom (IsRoundRobinChoice P.atom (Fin.castSucc j₀)) f S J' ∧
        S 0 = hat B₀) ↔
      ∃ B J, P.toLP.IsSimplexRunWithHist (P.toLP.IsCunninghamChoice j₀) f B J ∧ B 0 = B₀ ∧
        (∀ k ≤ f, S k = hat (B k)) ∧ ∀ k < f, J' k = Fin.castSucc (J k) :=
  IntLP.rules_cunningham_main P hP B₀ hB₀ j₀ f S J'

/-- Corollary 2 (`cor:intro-rules`), round robin / Cunningham, for the remaining initial label of
the
round-robin rule, the slack label `n+1`: it corresponds to Cunningham's rule with the initial
label `0` (the paper's label `1`, written `j₀` with `j₀ = 0`); both start with the natural order
of `[n]`. -/
theorem rules_cunningham_slack (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (j₀ : Fin n) (hj₀ : (j₀ : ℕ) = 0)
    (f : ℕ) (S : ℕ → Finset (Fin (n + 1))) (J' : ℕ → Fin (n + 1)) :
    (IsWolfeRunWithHist P.atom (IsRoundRobinChoice P.atom (Fin.last n)) f S J' ∧
        S 0 = hat B₀) ↔
      ∃ B J, P.toLP.IsSimplexRunWithHist (P.toLP.IsCunninghamChoice j₀) f B J ∧ B 0 = B₀ ∧
        (∀ k ≤ f, S k = hat (B k)) ∧ ∀ k < f, J' k = Fin.castSucc (J k) :=
  IntLP.rules_cunningham_slack_main P hP B₀ hB₀ j₀ hj₀ f S J'

/-- The steps of the random runs are well defined: at a feasible basis `B`, the pivot on an
improving label `j` has exactly one result `pivotTo B j`, and the major cycle at `B̂` that
inserts `j` has exactly one result, its hat. (So the `Classical.epsilon` in `pivotTo` and
`majorTo` chooses nothing.) -/
theorem rules_unique_steps (P : IntLP m n) (hP : P.IsAdmissible)
    (B : Finset (Fin n)) (hB : P.toLP.IsFeasibleBasis B) (j : Fin n)
    (hj : j ∈ P.toLP.improving B) :
    (∀ B', P.toLP.IsPivot B j B' ↔ B' = P.toLP.pivotTo B j) ∧
    (∀ S', MajorCycle P.atom (hat B) (Fin.castSucc j) S' ↔ S' = hat (P.toLP.pivotTo B j)) :=
  IntLP.rules_unique_steps_main P hP B hB j hj

/-- Corollary 2 (`cor:intro-rules`), random / Random-Edge: for every `k`, the distribution of the
corrals visited in the first `k` major cycles of the random rule from `B̂₀` is the
distribution of the hats of the bases visited in the first `k` pivots of Random-Edge
from `B₀`. -/
theorem rules_random_edge (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (k : ℕ) :
    Wolfe.randomRun P.atom (Wolfe.randomInsertion P.atom) k (hat B₀) =
      (P.toLP.randomRun P.toLP.randomEdge k B₀).map (List.map hat) :=
  IntLP.rules_random_edge_main P hP B₀ hB₀ k

/-- Corollary 2 (`cor:intro-rules`), random order / Random-Bland: the same as `rules_random_edge`
for
the random-order rule (uniformly random permutation of `[n+1]`) and Random-Bland (uniformly
random permutation of `[n]`). -/
theorem rules_random_bland (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (k : ℕ) :
    Wolfe.randomOrderRun P.atom k (hat B₀) =
      (P.toLP.randomBlandRun k B₀).map (List.map hat) :=
  IntLP.rules_random_bland_main P hP B₀ hB₀ k

/-! ## Appendix C.2 (`app:cor-rules`) (cap argument): the cap constraint

For an LP with integer data, rank `m ≥ 1`, a finite optimum, and only nondegenerate feasible
bases (such as the LPs of the MDPs used for the lower bounds), the capped LP `P.cap`
satisfies (A1)–(A3), and its simplex runs from `B₀ ∪ {cap}` are those of `P` from `B₀`. The
MDP-specific facts (that the MDP LPs have these properties) are cited, not formalized. -/

/-- Appendix C.2 (`app:cor-rules`) (cap argument): the capped LP is admissible. -/
theorem cap_admissible (P : IntLP m n) (hm : 1 ≤ m) (hrank : P.toLP.A.rank = m)
    (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (hnd : ∀ B, P.toLP.IsFeasibleBasis B → P.toLP.IsNondegenerate B) :
    P.cap.IsAdmissible :=
  IntLP.cap_admissible_main P hm hrank hopt hnd

/-- Appendix C.2 (`app:cor-rules`) (cap argument): every feasible basis `B` of `P` gives the
feasible basis
`B ∪ {cap}` of the capped LP with the same reduced costs (hence the same improving labels),
and the pivots of the capped LP at `B ∪ {cap}` are exactly the pivots of `P` at `B` with the
cap added (`x_cap` never leaves). -/
theorem cap_bases (P : IntLP m n) (hm : 1 ≤ m) (hrank : P.toLP.A.rank = m)
    (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (hnd : ∀ B, P.toLP.IsFeasibleBasis B → P.toLP.IsNondegenerate B)
    (B : Finset (Fin n)) (hB : P.toLP.IsFeasibleBasis B) :
    P.cap.toLP.IsFeasibleBasis (hat B) ∧
    (∀ j, P.cap.toLP.reducedCost (hat B) (Fin.castSucc j) = P.toLP.reducedCost B j) ∧
    P.cap.toLP.improving (hat B) = (P.toLP.improving B).map Fin.castSuccEmb ∧
    ∀ j' S', P.cap.toLP.IsPivot (hat B) j' S' ↔
      ∃ j B', j' = Fin.castSucc j ∧ P.toLP.IsPivot B j B' ∧ S' = hat B' :=
  IntLP.cap_bases_main P hm hrank hopt hnd B hB

/-- Appendix C.2 (`app:cor-rules`) (cap argument): the pivots of `P` from a feasible basis exist
and are unique (so the
`Classical.epsilon` in `pivotTo`, used in `cap_random_edge` and `cap_random_bland`, chooses
nothing), and lead to feasible bases. -/
theorem cap_unique_steps (P : IntLP m n) (hm : 1 ≤ m) (hrank : P.toLP.A.rank = m)
    (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (hnd : ∀ B, P.toLP.IsFeasibleBasis B → P.toLP.IsNondegenerate B)
    (B : Finset (Fin n)) (hB : P.toLP.IsFeasibleBasis B) (j : Fin n)
    (hj : j ∈ P.toLP.improving B) :
    (∀ B', P.toLP.IsPivot B j B' ↔ B' = P.toLP.pivotTo B j) ∧
    P.toLP.IsFeasibleBasis (P.toLP.pivotTo B j) :=
  ⟨(IntLP.cap_pivotTo P hm hrank hopt hnd B hB j hj).1,
    (IntLP.cap_pivotTo P hm hrank hopt hnd B hB j hj).2.1⟩

/-- Appendix C.2 (`app:cor-rules`) (cap argument), Zadeh's rule: the simplex runs (with entering
labels) of the capped
LP from `B₀ ∪ {cap}` are exactly those of `P` from `B₀`, with the cap added. -/
theorem cap_zadeh (P : IntLP m n) (hm : 1 ≤ m) (hrank : P.toLP.A.rank = m)
    (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (hnd : ∀ B, P.toLP.IsFeasibleBasis B → P.toLP.IsNondegenerate B)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (f : ℕ)
    (B' : ℕ → Finset (Fin (n + 1))) (J' : ℕ → Fin (n + 1)) :
    (P.cap.toLP.IsSimplexRunWithHist P.cap.toLP.IsZadehChoice f B' J' ∧ B' 0 = hat B₀) ↔
      ∃ B J, P.toLP.IsSimplexRunWithHist P.toLP.IsZadehChoice f B J ∧ B 0 = B₀ ∧
        (∀ k ≤ f, B' k = hat (B k)) ∧ ∀ k < f, J' k = Fin.castSucc (J k) :=
  IntLP.cap_zadeh_main P hm hrank hopt hnd B₀ hB₀ f B' J'

/-- Appendix C.2 (`app:cor-rules`) (cap argument), Cunningham's rule: as `cap_zadeh`. -/
theorem cap_cunningham (P : IntLP m n) (hm : 1 ≤ m) (hrank : P.toLP.A.rank = m)
    (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (hnd : ∀ B, P.toLP.IsFeasibleBasis B → P.toLP.IsNondegenerate B)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (j₀ : Fin n) (f : ℕ)
    (B' : ℕ → Finset (Fin (n + 1))) (J' : ℕ → Fin (n + 1)) :
    (P.cap.toLP.IsSimplexRunWithHist (P.cap.toLP.IsCunninghamChoice (Fin.castSucc j₀)) f B' J' ∧
        B' 0 = hat B₀) ↔
      ∃ B J, P.toLP.IsSimplexRunWithHist (P.toLP.IsCunninghamChoice j₀) f B J ∧ B 0 = B₀ ∧
        (∀ k ≤ f, B' k = hat (B k)) ∧ ∀ k < f, J' k = Fin.castSucc (J k) :=
  IntLP.cap_cunningham_main P hm hrank hopt hnd B₀ hB₀ j₀ f B' J'

/-- Appendix C.2 (`app:cor-rules`) (cap argument), Random-Edge: the distributions of the runs of
the capped LP from
`B₀ ∪ {cap}` and of `P` from `B₀` agree (mapped by `B ↦ B ∪ {cap}`). -/
theorem cap_random_edge (P : IntLP m n) (hm : 1 ≤ m) (hrank : P.toLP.A.rank = m)
    (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (hnd : ∀ B, P.toLP.IsFeasibleBasis B → P.toLP.IsNondegenerate B)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (k : ℕ) :
    P.cap.toLP.randomRun P.cap.toLP.randomEdge k (hat B₀) =
      (P.toLP.randomRun P.toLP.randomEdge k B₀).map (List.map hat) :=
  LP.randomEdge_transfer _ _ (fun B hB ↦ ⟨(IntLP.cap_bases_main P hm hrank hopt hnd B hB).2.2.1,
    fun j hj ↦ (IntLP.cap_pivotTo P hm hrank hopt hnd B hB j hj).2⟩) B₀ hB₀ k

/-- Appendix C.2 (`app:cor-rules`) (cap argument), Random-Bland: as `cap_random_edge`. -/
theorem cap_random_bland (P : IntLP m n) (hm : 1 ≤ m) (hrank : P.toLP.A.rank = m)
    (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (hnd : ∀ B, P.toLP.IsFeasibleBasis B → P.toLP.IsNondegenerate B)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (k : ℕ) :
    P.cap.toLP.randomBlandRun k (hat B₀) =
      (P.toLP.randomBlandRun k B₀).map (List.map hat) :=
  LP.randomBland_transfer _ _ (fun B hB ↦ ⟨(IntLP.cap_bases_main P hm hrank hopt hnd B hB).2.2.1,
    fun j hj ↦ (IntLP.cap_pivotTo P hm hrank hopt hnd B hB j hj).2⟩) B₀ hB₀ k

/-! ## Section 3 (`sec:equivalence`) (integrality discussion): scaling to integer data

Assumption (A1) is without loss of generality: multiplying row `i` of `(A, b)` by `r i > 0` and
`c` by `ω > 0` keeps the feasible set, the (feasible) bases and the pivots and multiplies the
reduced costs by `ω`, so the runs with all rules of Table 1 (`tab:wolfe-rules`) stay the same; and
rational data become integral for suitable `r, ω`. -/

/-- Section 3 (`sec:equivalence`) (integrality discussion): scaling keeps the feasible points, the
bases, the feasible
bases and the pivots, and multiplies the reduced costs at every basis by `ω`. -/
theorem scale_bases (P : LP m n) (r : Fin m → ℝ) (hr : ∀ i, 0 < r i) (ω : ℝ) (hω : 0 < ω) :
    (∀ x, (P.scale r ω).IsFeasible x ↔ P.IsFeasible x) ∧
    (∀ B, (P.scale r ω).IsBasis B ↔ P.IsBasis B) ∧
    (∀ B, (P.scale r ω).IsFeasibleBasis B ↔ P.IsFeasibleBasis B) ∧
    (∀ B, P.IsBasis B → ∀ j, (P.scale r ω).reducedCost B j = ω * P.reducedCost B j) ∧
    (∀ B j B', (P.scale r ω).IsPivot B j B' ↔ P.IsPivot B j B') :=
  ⟨P.scale_isFeasible_iff hr ω, P.scale_isBasis_iff hr ω, P.scale_isFeasibleBasis_iff hr ω,
    fun _ hB j ↦ P.scale_reducedCost hr ω hB j, P.scale_isPivot_iff hr hω⟩

/-- Section 3 (`sec:equivalence`) (integrality discussion): the simplex runs with the deterministic
rules of Table 1 (`tab:wolfe-rules`) (Dantzig, Bland, Zadeh, Cunningham) are the same before and
after scaling. -/
theorem scale_runs (P : LP m n) (r : Fin m → ℝ) (hr : ∀ i, 0 < r i) (ω : ℝ) (hω : 0 < ω) :
    (∀ f B, (P.scale r ω).IsSimplexRunWith (P.scale r ω).IsDantzigChoice f B ↔
      P.IsSimplexRunWith P.IsDantzigChoice f B) ∧
    (∀ ρ f B, (P.scale r ω).IsSimplexRunWith ((P.scale r ω).IsBlandChoice ρ) f B ↔
      P.IsSimplexRunWith (P.IsBlandChoice ρ) f B) ∧
    (∀ f B J, (P.scale r ω).IsSimplexRunWithHist (P.scale r ω).IsZadehChoice f B J ↔
      P.IsSimplexRunWithHist P.IsZadehChoice f B J) ∧
    (∀ j₀ f B J,
      (P.scale r ω).IsSimplexRunWithHist ((P.scale r ω).IsCunninghamChoice j₀) f B J ↔
        P.IsSimplexRunWithHist (P.IsCunninghamChoice j₀) f B J) :=
  scale_runs_main P hr hω

/-- Section 3 (`sec:equivalence`) (integrality discussion): the distributions of the runs of
Random-Edge and Random-Bland
from a feasible basis are the same before and after scaling (if the optimum is finite, so that
every pivot exists). -/
theorem scale_random_runs (P : LP m n) (r : Fin m → ℝ) (hr : ∀ i, 0 < r i) (ω : ℝ)
    (hω : 0 < ω) (hopt : ∃ x, P.IsOptimalSolution x) (B : Finset (Fin n))
    (hB : P.IsFeasibleBasis B) (k : ℕ) :
    (P.scale r ω).randomRun (P.scale r ω).randomEdge k B = P.randomRun P.randomEdge k B ∧
    (P.scale r ω).randomBlandRun k B = P.randomBlandRun k B :=
  scale_random_runs_main P hr hω hopt B hB k

/-- Section 3 (`sec:equivalence`) (integrality discussion): an LP with rational data becomes an LP
with integer data after
scaling the rows and the costs by suitable positive numbers. -/
theorem scale_integral (P : LP m n) (hA : ∀ i j, ∃ q : ℚ, P.A i j = q)
    (hb : ∀ i, ∃ q : ℚ, P.b i = q) (hc : ∀ j, ∃ q : ℚ, P.c j = q) :
    ∃ (r : Fin m → ℝ) (ω : ℝ) (Q : IntLP m n), (∀ i, 0 < r i) ∧ 0 < ω ∧
      Q.toLP = P.scale r ω :=
  scale_integral_main P hA hb hc

/-! ## Appendix C.2 (`app:cor-rules`) (shortest-atom construction): starting at the minimum-norm
atom

Notation (see `Defs/Shield.lean`): `B₀ = basisOf e`; (LP⁺) is `P.shieldLP e` with the
shield `ω = Fin.last n`, so `B ∪ {ω}` is `hat B`; its atoms of Equation 31 (`eq:shield-atoms`) are
`(P.shieldLP e).atom` with labels `Fin (n+2)`, where the original label `k` is
`k.castSucc.castSucc`, the shield is `(Fin.last n).castSucc`, and the slack label
(the paper's `n+2`) is `Fin.last (n+1)`; the corral of `B ∪ {ω}` is `hat (hat B)`.

"Polynomial bit length" and "computed in polynomial time" are replaced, as in
`equivalence_size`, by explicit bounds on the absolute values of the entries, in
terms of `W = P.maxEntry` (the largest absolute value of an entry of `A, b, c`,
but at least `2`): the bit length of every entry is then polynomial in the bit
length of `(A, b, c)`.
-/

/-- Lemma 12 (`lem:shield-lp`): (LP⁺) is admissible and its data have polynomial bit
length; its feasible bases are the sets `B ∪ {ω}` for the feasible bases `B` of
(LP); the reduced costs of the labels in `[n]` at `B ∪ {ω}` are `Δ₀` times those at
`B` (for every basis `B`); and for every improving label `j` at a feasible basis
`B`, the pivots at `B` and at `B ∪ {ω}` have the same leaving labels. -/
theorem shield_lp (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e)) :
    (P.shieldLP e).IsAdmissible ∧
    (P.shieldLP e).maxEntry ≤ ((m + 1) * P.maxEntry) ^ (2 * m + 2) ∧
    (∀ B' : Finset (Fin (n + 1)), (P.shieldLP e).toLP.IsFeasibleBasis B' ↔
      ∃ B, P.toLP.IsFeasibleBasis B ∧ B' = hat B) ∧
    (∀ B, P.toLP.IsBasis B → ∀ j : Fin n,
      (P.shieldLP e).toLP.reducedCost (hat B) (Fin.castSucc j) =
        P.Delta0 e * P.toLP.reducedCost B j) ∧
    (∀ B, P.toLP.IsFeasibleBasis B → ∀ j ∈ P.toLP.improving B, ∀ i' : Fin (n + 1),
      (P.shieldLP e).toLP.IsLeavingLabel (hat B) (Fin.castSucc j) i' ↔
        ∃ i, i' = Fin.castSucc i ∧ P.toLP.IsLeavingLabel B j i) :=
  IntLP.shield_lp_main P hP e hB₀

/-- Lemma 13 (`lem:init`)(a): every set `S` with `n+2 ∈ S ⊆ B₀ ∪ {ω, n+2}` is a corral
of the atoms of Equation 31 (`eq:shield-atoms`). -/
theorem init_a (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    (S : Finset (Fin (n + 2))) (hS : Fin.last (n + 1) ∈ S) (hSB : S ⊆ hat (hat (basisOf e))) :
    IsCorral (P.shieldLP e).atom S :=
  IntLP.init_a_main P hP e hB₀ S hS hSB

/-- Lemma 13 (`lem:init`)(b): if moreover `ω ∉ S`, then the improving atoms at `w_S` are
those of the labels in `(B₀ ∪ {ω}) \ S`, with the gaps `g_ℓ(w_S) = -N⁴ Δ₀ β_ℓ`,
where `β = b⁺/T` (`N`, `T` of (LP⁺); the label `e i` has the row `i`, and `ω` has the
last row, with `b⁺_ω = 1`); and every major cycle at `S` that inserts such a label
`ℓ` has no minor cycle and ends at the corral `S ∪ {ℓ}`. -/
theorem init_b (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    (S : Finset (Fin (n + 2))) (hS : Fin.last (n + 1) ∈ S) (hSB : S ⊆ hat (hat (basisOf e)))
    (hω : Fin.castSucc (Fin.last n) ∉ S) :
    improving (P.shieldLP e).atom (affineMin (P.shieldLP e).atom S) =
      (hat (basisOf e)).map Fin.castSuccEmb \ S ∧
    (∀ ℓ : Fin (m + 1), Fin.castSucc (Fin.snoc (α := fun _ ↦ Fin (n + 1))
          (fun i ↦ Fin.castSucc (e i)) (Fin.last n) ℓ) ∉ S →
      gap (P.shieldLP e).atom (Fin.castSucc (Fin.snoc (α := fun _ ↦ Fin (n + 1))
          (fun i ↦ Fin.castSucc (e i)) (Fin.last n) ℓ)) (affineMin (P.shieldLP e).atom S) =
        -((P.shieldLP e).N : ℝ) ^ 4 * P.Delta0 e * ((P.shieldLP e).b ℓ / (P.shieldLP e).T)) ∧
    ∀ ℓ ∈ improving (P.shieldLP e).atom (affineMin (P.shieldLP e).atom S),
      ∀ S', MajorCycle (P.shieldLP e).atom S ℓ S' ↔ S' = insert ℓ S :=
  IntLP.init_b_main P hP e hB₀ S hS hSB hω

/-- Lemma 13 (`lem:init`)(c): the slack atom `p_{n+2}` is the unique atom of minimum norm. -/
theorem init_c (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e)) :
    ∀ j ≠ Fin.last (n + 1),
      normSq ((P.shieldLP e).atom (Fin.last (n + 1))) < normSq ((P.shieldLP e).atom j) :=
  IntLP.init_c_main P hP e hB₀

/-- Lemma 14 (`lem:init-run`), linopt rule: the atoms of Equation 31 (`eq:shield-atoms`) are
integral and of
polynomial size, and `p_{n+2}` is the unique shortest atom. For every Wolfe run with
the linopt rule (any tie-breaking) from `{n+2}`, the first `m+1` major cycles insert
the labels of `B₀ ∪ {ω}` one by one without minor cycles (stated as
`S_{k+1} = S_k ∪ {ℓ}` with `ℓ ∉ S_k`: a minor cycle would delete a label), and then the corrals are
the sets `B_k ∪ {ω, n+2}` for a simplex run `B₀, …, B_f` on (LP) with Dantzig's
rule. Conversely, every simplex run with Dantzig's rule from `B₀` arises in this
way. -/
theorem init_linopt (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e)) :
    (∀ j k, ∃ z : ℤ, (P.shieldLP e).atom j k = z) ∧
    (∀ j k, |(P.shieldLP e).atom j k| ≤
      (((m + 1) * P.maxEntry : ℕ) : ℝ) ^ (100 * (m + 2) ^ 3)) ∧
    (∀ j ≠ Fin.last (n + 1),
      normSq ((P.shieldLP e).atom (Fin.last (n + 1))) < normSq ((P.shieldLP e).atom j)) ∧
    (∀ f S, IsWolfeRunWith (P.shieldLP e).atom (IsLinoptChoice (P.shieldLP e).atom) f S →
      S 0 = {Fin.last (n + 1)} →
      m + 1 ≤ f ∧
      (∀ k < m + 1, ∃ ℓ ∈ (hat (basisOf e)).map Fin.castSuccEmb,
        ℓ ∉ S k ∧ S (k + 1) = insert ℓ (S k)) ∧
      ∃ B, P.toLP.IsSimplexRunWith P.toLP.IsDantzigChoice (f - (m + 1)) B ∧
        B 0 = basisOf e ∧ ∀ k ≤ f - (m + 1), S (m + 1 + k) = hat (hat (B k))) ∧
    (∀ f B, P.toLP.IsSimplexRunWith P.toLP.IsDantzigChoice f B → B 0 = basisOf e →
      ∃ S, IsWolfeRunWith (P.shieldLP e).atom (IsLinoptChoice (P.shieldLP e).atom)
          (m + 1 + f) S ∧
        S 0 = {Fin.last (n + 1)} ∧ ∀ k ≤ f, S (m + 1 + k) = hat (hat (B k))) :=
  InitRuns.init_linopt_main P hP e hB₀

/-- Lemma 14 (`lem:init-run`), least-label rule: the same as `init_linopt` for the
least-label rule for an order (rank function `ρ`) of the labels of the atoms in
which `ω` comes after all labels of `[n]`, and Bland's rule for the induced order
of `[n]`. -/
theorem init_leastLabel (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    (ρ : Fin (n + 2) → ℕ) (hρ : ∀ k : Fin n, ρ k.castSucc.castSucc < ρ (Fin.last n).castSucc) :
    (∀ f S, IsWolfeRunWith (P.shieldLP e).atom
        (IsLeastLabelChoice (P.shieldLP e).atom ρ) f S →
      S 0 = {Fin.last (n + 1)} →
      m + 1 ≤ f ∧
      (∀ k < m + 1, ∃ ℓ ∈ (hat (basisOf e)).map Fin.castSuccEmb,
        ℓ ∉ S k ∧ S (k + 1) = insert ℓ (S k)) ∧
      ∃ B, P.toLP.IsSimplexRunWith (P.toLP.IsBlandChoice fun k ↦ ρ k.castSucc.castSucc)
          (f - (m + 1)) B ∧
        B 0 = basisOf e ∧ ∀ k ≤ f - (m + 1), S (m + 1 + k) = hat (hat (B k))) ∧
    (∀ f B, P.toLP.IsSimplexRunWith (P.toLP.IsBlandChoice fun k ↦ ρ k.castSucc.castSucc) f B →
      B 0 = basisOf e →
      ∃ S, IsWolfeRunWith (P.shieldLP e).atom (IsLeastLabelChoice (P.shieldLP e).atom ρ)
          (m + 1 + f) S ∧
        S 0 = {Fin.last (n + 1)} ∧ ∀ k ≤ f, S (m + 1 + k) = hat (hat (B k))) :=
  InitRuns.init_leastLabel_main P hP e hB₀ ρ hρ

/-- Lemma 16 (`lem:weighted`)(a): (LP̃⁺) is admissible, its data have polynomial bit
length, its feasible bases are the sets `B ∪ {ω}` for the feasible bases `B` of
(LP), its improving labels at `B ∪ {ω}` are those at `B`, and for every improving
label, the pivots at `B` and at `B ∪ {ω}` have the same leaving labels. -/
theorem weighted_a (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e)) (σ : Equiv.Perm (Fin n)) :
    (P.weightedLP e σ).IsAdmissible ∧
    (P.weightedLP e σ).maxEntry ≤ (n + 1) * ((m + 1) * P.maxEntry) ^ (2 * m + 2) ∧
    (∀ B' : Finset (Fin (n + 1)), (P.weightedLP e σ).toLP.IsFeasibleBasis B' ↔
      ∃ B, P.toLP.IsFeasibleBasis B ∧ B' = hat B) ∧
    (∀ B, P.toLP.IsFeasibleBasis B →
      (P.weightedLP e σ).toLP.improving (hat B) = (P.toLP.improving B).map Fin.castSuccEmb) ∧
    (∀ B, P.toLP.IsFeasibleBasis B → ∀ j ∈ P.toLP.improving B, ∀ i' : Fin (n + 1),
      (P.weightedLP e σ).toLP.IsLeavingLabel (hat B) (Fin.castSucc j) i' ↔
        ∃ i, i' = Fin.castSucc i ∧ P.toLP.IsLeavingLabel B j i) :=
  IntLP.weighted_a_main P hP e hB₀ σ

/-- Lemma 16 (`lem:weighted`)(b): every set `S` with `n+2 ∈ S ⊆ B₀ ∪ {ω, n+2}` is a corral
of the weighted atoms of Equation 36 (`eq:weighted-atoms`); if `ω ∉ S`, the improving atoms at `w_S`
are those of the labels in `(B₀ ∪ {ω}) \ S`, and every major cycle at `S` that
inserts such a label `ℓ` has no minor cycle and ends at the corral `S ∪ {ℓ}`. -/
theorem weighted_b (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e)) (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin (n + 2))) (hS : Fin.last (n + 1) ∈ S) (hSB : S ⊆ hat (hat (basisOf e))) :
    IsCorral (P.weightedLP e σ).atom S ∧
    (Fin.castSucc (Fin.last n) ∉ S →
      improving (P.weightedLP e σ).atom (affineMin (P.weightedLP e σ).atom S) =
        (hat (basisOf e)).map Fin.castSuccEmb \ S ∧
      ∀ ℓ ∈ improving (P.weightedLP e σ).atom (affineMin (P.weightedLP e σ).atom S),
        ∀ S', MajorCycle (P.weightedLP e σ).atom S ℓ S' ↔ S' = insert ℓ S) :=
  IntLP.weighted_b_main P hP e hB₀ σ S hS hSB

/-- Lemma 16 (`lem:weighted`)(c): the norms of the weighted atoms increase strictly in the
order: first the slack label `n+2`, then `[n]` ordered by `≺` (given by `σ`), then
`ω`. -/
theorem weighted_c (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e)) (σ : Equiv.Perm (Fin n)) :
    let p := (P.weightedLP e σ).atom
    (∀ k : Fin n, normSq (p (Fin.last (n + 1))) < normSq (p k.castSucc.castSucc)) ∧
    (∀ k k' : Fin n, σ k < σ k' → normSq (p k.castSucc.castSucc) < normSq (p k'.castSucc.castSucc)) ∧
    (∀ k : Fin n, normSq (p k.castSucc.castSucc) < normSq (p (Fin.last n).castSucc)) :=
  IntLP.weighted_c_main P hP e hB₀ σ

/-- Lemma 17 (`lem:minnorm`): the weighted atoms of Equation 36 (`eq:weighted-atoms`) are
integral, of
polynomial size, and have pairwise distinct norms. For every Wolfe run with the
minnorm rule from the shortest atom `p_{n+2}`, the first `m+1` major cycles insert
the labels of `B₀ ∪ {ω}` one by one without minor cycles, and then the corrals are
the sets `B_k ∪ {ω, n+2}` for a simplex run `B₀, …, B_f` on (LP) with Bland's rule
for `≺` (given by `σ`). Conversely, every such simplex run arises in this way. -/
theorem minnorm (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e)) (σ : Equiv.Perm (Fin n)) :
    (∀ j k, ∃ z : ℤ, (P.weightedLP e σ).atom j k = z) ∧
    (∀ j k, |(P.weightedLP e σ).atom j k| ≤
      (((n + 1) * (m + 1) * P.maxEntry : ℕ) : ℝ) ^ (100 * (m + 2) ^ 3)) ∧
    (∀ j k, j ≠ k → normSq ((P.weightedLP e σ).atom j) ≠ normSq ((P.weightedLP e σ).atom k)) ∧
    (∀ j ≠ Fin.last (n + 1),
      normSq ((P.weightedLP e σ).atom (Fin.last (n + 1))) < normSq ((P.weightedLP e σ).atom j)) ∧
    (∀ f S, IsWolfeRunWith (P.weightedLP e σ).atom (IsMinnormChoice (P.weightedLP e σ).atom) f S →
      S 0 = {Fin.last (n + 1)} →
      m + 1 ≤ f ∧
      (∀ k < m + 1, ∃ ℓ ∈ (hat (basisOf e)).map Fin.castSuccEmb,
        ℓ ∉ S k ∧ S (k + 1) = insert ℓ (S k)) ∧
      ∃ B, P.toLP.IsSimplexRunWith (P.toLP.IsBlandChoice fun k ↦ (σ k : ℕ)) (f - (m + 1)) B ∧
        B 0 = basisOf e ∧ ∀ k ≤ f - (m + 1), S (m + 1 + k) = hat (hat (B k))) ∧
    (∀ f B, P.toLP.IsSimplexRunWith (P.toLP.IsBlandChoice fun k ↦ (σ k : ℕ)) f B →
      B 0 = basisOf e →
      ∃ S, IsWolfeRunWith (P.weightedLP e σ).atom (IsMinnormChoice (P.weightedLP e σ).atom)
          (m + 1 + f) S ∧
        S 0 = {Fin.last (n + 1)} ∧ ∀ k ≤ f, S (m + 1 + k) = hat (hat (B k))) :=
  InitRuns.minnorm_main P hP e hB₀ σ

/-! ## The Klee–Minty cube -/

/-- The Klee–Minty LP Equation 34 (`eq:km`) satisfies (A1)–(A3) (stated before Lemma 15 (`lem:km`)),
and `B₀ = {s_1, …, s_n}` is a feasible basis. -/
theorem km_admissible (n : ℕ) (hn : 1 ≤ n) :
    (kleeMinty n).IsAdmissible ∧ (kleeMinty n).toLP.IsFeasibleBasis (basisOf (kmSlack n)) :=
  KM.admissible n hn

/-- Lemma 15 (`lem:km`), Dantzig's rule: on Equation 34 (`eq:km`), started at `B₀ = {s_1, …, s_n}`,
Dantzig's rule performs `2ⁿ - 1` pivots (there is a run; every run has this
length; every partial run is at most this long), and every choice of Dantzig's
rule is unique (at every feasible basis, at most one label may be chosen). -/
theorem km_dantzig (n : ℕ) (hn : 1 ≤ n) :
    (∃ f B, (kleeMinty n).toLP.IsSimplexRunWith (kleeMinty n).toLP.IsDantzigChoice f B ∧
      B 0 = basisOf (kmSlack n)) ∧
    (∀ f B, (kleeMinty n).toLP.IsSimplexRunWith (kleeMinty n).toLP.IsDantzigChoice f B →
      B 0 = basisOf (kmSlack n) → f = 2 ^ n - 1) ∧
    (∀ f B, (kleeMinty n).toLP.IsPartialSimplexRunWith (kleeMinty n).toLP.IsDantzigChoice f B →
      B 0 = basisOf (kmSlack n) → f ≤ 2 ^ n - 1) ∧
    (∀ B, (kleeMinty n).toLP.IsFeasibleBasis B → ∀ j j',
      (kleeMinty n).toLP.IsDantzigChoice B j → (kleeMinty n).toLP.IsDantzigChoice B j' → j = j') :=
  KM.dantzig n hn

/-- Lemma 15 (`lem:km`), Bland's rule for the order `x_1 ≺ s_1 ≺ … ≺ x_n ≺ s_n` (the natural
order of the labels `Fin (2n)`): started at `B₀`, it performs `2ⁿ - 1` pivots. -/
theorem km_bland (n : ℕ) (hn : 1 ≤ n) :
    (∃ f B, (kleeMinty n).toLP.IsSimplexRunWith ((kleeMinty n).toLP.IsBlandChoice Fin.val) f B ∧
      B 0 = basisOf (kmSlack n)) ∧
    (∀ f B, (kleeMinty n).toLP.IsSimplexRunWith ((kleeMinty n).toLP.IsBlandChoice Fin.val) f B →
      B 0 = basisOf (kmSlack n) → f = 2 ^ n - 1) ∧
    (∀ f B, (kleeMinty n).toLP.IsPartialSimplexRunWith
        ((kleeMinty n).toLP.IsBlandChoice Fin.val) f B →
      B 0 = basisOf (kmSlack n) → f ≤ 2 ^ n - 1) :=
  KM.bland n hn

/-- Lemma 18 (`lem:km-start`), linopt rule: for every `n ≥ 1`, there are `2n+2` integer atoms
in `ℤ^{n+2}` with encoding length polynomial in `n` (every entry has absolute value
at most `10^{600 (n+2)⁴}`) and a unique atom `p_{k₀}` of minimum norm, such that
Wolfe's method with the linopt rule, started at this atom, visits exactly
`2ⁿ + n + 1` corrals, for every rule for breaking ties: a run exists; every run
`S_0, …, S_f` consists of `f + 1 = 2ⁿ + n + 1` distinct corrals; and every partial
run is at most this long (so the method always stops). -/
theorem km_linopt (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Fin (2 * n + 2) → Fin (n + 2) → ℝ,
      (∀ j k, ∃ z : ℤ, p j k = z) ∧ (∀ j k, |p j k| ≤ (10 : ℝ) ^ (600 * (n + 2) ^ 4)) ∧
      ∃ k₀, (∀ j ≠ k₀, normSq (p k₀) < normSq (p j)) ∧
        (∃ f S, IsWolfeRunWith p (IsLinoptChoice p) f S ∧ S 0 = {k₀}) ∧
        (∀ f S, IsWolfeRunWith p (IsLinoptChoice p) f S → S 0 = {k₀} →
          f + 1 = 2 ^ n + n + 1 ∧ Set.InjOn S (Set.Iic f)) ∧
        (∀ f S, IsPartialWolfeRunWith p (IsLinoptChoice p) f S → S 0 = {k₀} → f ≤ 2 ^ n + n) :=
  InitRuns.km_linopt_main hn

/-- Lemma 18 (`lem:km-start`), minnorm rule: the same as `km_linopt` for the minnorm rule, on
other atoms, which moreover have pairwise distinct norms. -/
theorem km_minnorm (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Fin (2 * n + 2) → Fin (n + 2) → ℝ,
      (∀ j k, ∃ z : ℤ, p j k = z) ∧ (∀ j k, |p j k| ≤ (10 : ℝ) ^ (600 * (n + 2) ^ 4)) ∧
      (∀ j k, j ≠ k → normSq (p j) ≠ normSq (p k)) ∧
      ∃ k₀, (∀ j ≠ k₀, normSq (p k₀) < normSq (p j)) ∧
        (∃ f S, IsWolfeRunWith p (IsMinnormChoice p) f S ∧ S 0 = {k₀}) ∧
        (∀ f S, IsWolfeRunWith p (IsMinnormChoice p) f S → S 0 = {k₀} →
          f + 1 = 2 ^ n + n + 1 ∧ Set.InjOn S (Set.Iic f)) ∧
        (∀ f S, IsPartialWolfeRunWith p (IsMinnormChoice p) f S → S 0 = {k₀} → f ≤ 2 ^ n + n) :=
  InitRuns.km_minnorm_main hn

/-! ## Appendix C.3 (`app:nnls`): nonnegative least squares and Lawson–Hanson

Notation (see `Defs/LawsonHanson.lean`): for atoms `p`, `E = nnlsMatrix p` has the
columns `(p_j, 1)ᵀ`, and `f = nnlsRhs D = (0, 1)ᵀ`. -/

/-- Lemma 19 (`lem:nnls-ls`): for an affinely independent support `S`, the columns of `E_S`
are linearly independent; the vector that vanishes outside `S` and minimizes
`‖Eζ − f‖` is (exactly) `ζ^S = λ^{*S}/(1 + ‖w_S‖²)`; and at `ν = ζ^S`, the vector
`r = Eᵀ(f − Eν)` has the entries `r_j = −g_j(w_S)/(1 + ‖w_S‖²)`. -/
theorem nnls_ls {N D : ℕ} (p : Fin N → Fin D → ℝ) (S : Finset (Fin N)) (hS : S.Nonempty)
    (hAI : IsAffinelyIndependent p S) :
    LinearIndependent ℝ (fun i : S ↦ fun r ↦ nnlsMatrix p r i) ∧
    (∀ ζ, LH.IsLsSolOf (nnlsMatrix p) (nnlsRhs D) S ζ ↔
      ζ = (1 + normSq (affineMin p S))⁻¹ • affineCoeffs p S) ∧
    ∀ j, LH.resid (nnlsMatrix p) (nnlsRhs D) ((1 + normSq (affineMin p S))⁻¹ • affineCoeffs p S) j =
      -gap p j (affineMin p S) / (1 + normSq (affineMin p S)) :=
  nnls_ls_main p S hS hAI

/-- Lemma 20 (`lem:lh-wolfe`), one major cycle: let `S` be a corral, and let the improving
label `j` be added (by Wolfe's method at `w_S`, and by Lawson–Hanson at `ν = ζ^S`).
If every minor cycle of this major cycle sets only one coefficient to zero, then the
inner iterations of Lawson–Hanson are exactly the minor cycles: every state reachable
by inner iterations is `(F, ν) = (S', c λ)` for a state `(S', λ)` reachable by minor
cycles and some `c > 0`, and conversely every state reachable by minor cycles has such
a counterpart (so every inner iteration removes exactly the label that the
corresponding minor cycle deletes); and Lawson–Hanson ends the outer iteration
with `F = S'` exactly if the major cycle ends at the corral `S'`. -/
theorem lh_wolfe_major {N D : ℕ} (p : Fin N → Fin D → ℝ) (S : Finset (Fin N))
    (hS : IsCorral p S) (j : Fin N) (hj : j ∈ improving p (affineMin p S))
    (hsingle : ∀ s s', Relation.ReflTransGen (MinorCycle p) ⟨insert j S, affineCoeffs p S⟩ s →
      MinorCycle p s s' → ∀ i ∈ s.S, ∀ i' ∈ s.S, s'.lam i = 0 → s'.lam i' = 0 → i = i') :
    (∀ s' : LH.State N, Relation.ReflTransGen (LH.InnerStep (nnlsMatrix p) (nnlsRhs D))
        ⟨.inner, insert j S, LH.lsSol (nnlsMatrix p) (nnlsRhs D) S⟩ s' →
      ∃ (w : Wolfe.State N) (c : ℝ), 0 < c ∧
        Relation.ReflTransGen (MinorCycle p) ⟨insert j S, affineCoeffs p S⟩ w ∧
        s' = ⟨.inner, w.S, c • w.lam⟩) ∧
    (∀ w : Wolfe.State N, Relation.ReflTransGen (MinorCycle p) ⟨insert j S, affineCoeffs p S⟩ w →
      ∃ c : ℝ, 0 < c ∧ Relation.ReflTransGen (LH.InnerStep (nnlsMatrix p) (nnlsRhs D))
        ⟨.inner, insert j S, LH.lsSol (nnlsMatrix p) (nnlsRhs D) S⟩ ⟨.inner, w.S, c • w.lam⟩) ∧
    ∀ S' : Finset (Fin N),
      (∃ s' : LH.State N, Relation.ReflTransGen (LH.InnerStep (nnlsMatrix p) (nnlsRhs D))
          ⟨.inner, insert j S, LH.lsSol (nnlsMatrix p) (nnlsRhs D) S⟩ s' ∧
        LH.AcceptStep (nnlsMatrix p) (nnlsRhs D) s'
          ⟨.outer, S', LH.lsSol (nnlsMatrix p) (nnlsRhs D) S'⟩) ↔
      MajorCycle p S j S' :=
  lh_wolfe_major_main p S hS j hj hsingle

/-- Lemma 20 (`lem:lh-wolfe`), runs: consider Lawson–Hanson on Equation 37 (`eq:nnls`) and Wolfe's
method
with the linopt rule started at the first label `k` that Lawson–Hanson adds, with any
tie-breaking on both sides. If, in every major cycle of every such Wolfe run, every
minor cycle sets only one coefficient to zero, then the executions of Lawson–Hanson
whose first added label is `k` and the Wolfe runs from `{k}` (with inserted labels
`js 0, …, js (f-1)`) correspond: the sets `F` at the beginnings of the outer iterations
are `∅, S_0, S_1, …, S_f`, both methods add the same labels in the same order
(`k, js 0, …, js (f-1)`), and the number of outer iterations that add a
label equals the number `f + 1` of corrals of the Wolfe run. -/
theorem lh_wolfe {N D : ℕ} (p : Fin N → Fin D → ℝ) (k : Fin N)
    (hsingle : ∀ f S, IsPartialWolfeRunWith p (IsLinoptChoice p) f S → S 0 = {k} →
      ∀ j, IsLinoptChoice p (S f) j → ∀ s s',
        Relation.ReflTransGen (MinorCycle p) ⟨insert j (S f), affineCoeffs p (S f)⟩ s →
        MinorCycle p s s' → ∀ i ∈ s.S, ∀ i' ∈ s.S, s'.lam i = 0 → s'.lam i' = 0 → i = i') :
    (∀ T s, LH.IsExecution (nnlsMatrix p) (nnlsRhs D) T s → (s 1).F = {k} →
      ∃ (f : ℕ) (S : ℕ → Finset (Fin N)) (js : ℕ → Fin N),
        IsWolfeRunWith p (IsLinoptChoice p) f S ∧ S 0 = {k} ∧
        (∀ l < f, IsLinoptChoice p (S l) (js l) ∧ MajorCycle p (S l) (js l) (S (l + 1))) ∧
        LH.outerSets T s = ∅ :: (List.range (f + 1)).map S ∧
        LH.addedSets T s = {k} :: (List.range f).map (fun l ↦ {js l}) ∧
        LH.numAdds T s = f + 1) ∧
    (∀ f (S : ℕ → Finset (Fin N)) (js : ℕ → Fin N),
      IsWolfeRunWith p (IsLinoptChoice p) f S → S 0 = {k} →
      (∀ l < f, IsLinoptChoice p (S l) (js l) ∧ MajorCycle p (S l) (js l) (S (l + 1))) →
      ∃ T s, LH.IsExecution (nnlsMatrix p) (nnlsRhs D) T s ∧ (s 1).F = {k} ∧
        LH.outerSets T s = ∅ :: (List.range (f + 1)).map S ∧
        LH.addedSets T s = {k} :: (List.range f).map (fun l ↦ {js l}) ∧
        LH.numAdds T s = f + 1) :=
  lh_wolfe_main p k hsingle

/-- Corollary 3 (`cor:intro-nnls`): for every `n ≥ 1`, there is an integer matrix `E` with `n+3`
rows
and `2n+2` columns, of encoding length polynomial in `n` (entries of absolute value at
most `2 · 10^{600 (n+2)⁴}`), on which the Lawson–Hanson algorithm for
`min {‖Eν − e_{n+3}‖ : ν ≥ 0}` performs exactly `2ⁿ + n + 1` outer iterations that add
a label, for every rule for breaking ties: an execution exists, every execution has
this number of outer iterations that add a label, and every partial execution has at
most `3 (2ⁿ + n + 1)` steps (so the algorithm always stops). -/
theorem nnls (n : ℕ) (hn : 1 ≤ n) :
    ∃ E : Matrix (Fin (n + 3)) (Fin (2 * n + 2)) ℤ,
      (∀ r j, |E r j| ≤ 2 * 10 ^ (600 * (n + 2) ^ 4)) ∧
      (∃ T s, LH.IsExecution (E.map fun z : ℤ ↦ (z : ℝ)) (nnlsRhs (n + 2)) T s) ∧
      (∀ T s, LH.IsExecution (E.map fun z : ℤ ↦ (z : ℝ)) (nnlsRhs (n + 2)) T s →
        LH.numAdds T s = 2 ^ n + n + 1) ∧
      (∀ T s, LH.IsPartialExecution (E.map fun z : ℤ ↦ (z : ℝ)) (nnlsRhs (n + 2)) T s →
        T ≤ 3 * (2 ^ n + n + 1)) :=
  nnls_main n hn

end WolfeSimplex
