import WolfeSimplex.Proofs.SimplexFacts
import WolfeSimplex.Proofs.WolfeFacts
import WolfeSimplex.Proofs.Numbers
import WolfeSimplex.Proofs.Cramer

/-!
# The corral `B̂` of a basis `B` (paper: Steps 1–3 of Section 3.2 (`sec:atoms`))

For a basis `B` of the original LP we write down the quantities of the basis
`S = B̂` of the induced LP explicitly, via the formulas of Lemma 2 (`lem:hom`):
* `lamHat B = (x^B, T - 1ᵀx^B)/T`        (`λ^S`, Lemma 2 (`lem:hom`)(a)),
* `hHat B = C + (y^B)ᵀb/T`               (`h^S`, Lemma 2 (`lem:hom`)(b), `v^S = y^B`),
* `dirHat B j = (d^{B,j}, -1ᵀd^{B,j})`  (`d^{S,j}`),
* `uHat B = (u, -1ᵀu)` with `A u = y^B`, `u` vanishing off `B` (`u^S`),
* `eps B = h/(N² + ‖y‖²)`, `lamStar B = lamHat B - eps B • uHat B`, and
  `wHat B = (N s, -N² ε y)` with `s = N² ε`        (Equation 15 (`eq:projection-quantities`)).
We prove Lemma 4 (`lem:corral`) (`affineMin = wHat`, `affineCoeffs = lamStar`, the gap
formula) and Lemma 5 (`lem:bases-corrals`) (`B̂` is a corral for a feasible basis).
-/

namespace WolfeSimplex.IntLP

open Finset Matrix Wolfe

variable {m n : ℕ} (P : IntLP m n)

/-! ### Basic facts about `toLP`, `hat`, `Fin.snoc` -/

@[simp] lemma toLP_A (i : Fin m) (j : Fin n) : P.toLP.A i j = (P.A i j : ℝ) := by
  simp [toLP]

@[simp] lemma toLP_b (i : Fin m) : P.toLP.b i = (P.b i : ℝ) := rfl

@[simp] lemma toLP_c (j : Fin n) : P.toLP.c j = (P.c j : ℝ) := rfl

@[simp] lemma toLP_col (j : Fin n) (i : Fin m) : P.toLP.col j i = (P.A i j : ℝ) := by
  simp [LP.col]

omit P in
@[simp] lemma castSucc_mem_hat {B : Finset (Fin n)} {k : Fin n} :
    Fin.castSucc k ∈ hat B ↔ k ∈ B := by
  simp [hat, Fin.castSucc_ne_last]

omit P in
@[simp] lemma last_mem_hat {B : Finset (Fin n)} : Fin.last n ∈ hat B := by
  simp [hat]

omit P in
lemma card_hat (B : Finset (Fin n)) : (hat B).card = B.card + 1 := by
  rw [hat, card_insert_of_notMem, card_map]
  simp [Fin.castSucc_ne_last]

omit P in
/-- A vector `snoc x t` vanishes off `hat B` if `x` vanishes off `B`. -/
lemma snoc_eq_zero_of_not_mem_hat {B : Finset (Fin n)} {x : Fin n → ℝ} {t : ℝ}
    (hx : ∀ k ∉ B, x k = 0) : ∀ k ∉ hat B, (Fin.snoc (α := fun _ ↦ ℝ) x t) k = 0 := by
  intro k hk
  induction k using Fin.lastCases with
  | last => exact absurd last_mem_hat hk
  | cast k => simpa using hx k (by simpa using hk)

omit P in
lemma sum_snoc (x : Fin n → ℝ) (t : ℝ) :
    ∑ k, (Fin.snoc (α := fun _ ↦ ℝ) x t) k = ∑ k, x k + t := by
  simp [Fin.sum_univ_castSucc]

/-! ### Linear combinations of the atoms -/

/-- `∑_k λ_k α_k`, the violation of the homogeneous constraints. -/
noncomputable def acomb (lam : Fin (n + 1) → ℝ) : Fin m → ℝ :=
  fun i ↦ ∑ k, lam k * P.alpha k i

/-- `γᵀλ`, the objective value in the induced LP. -/
noncomputable def gcomb (lam : Fin (n + 1) → ℝ) : ℝ :=
  ∑ k, lam k * (P.gamma k : ℝ)

/-- The penalty identity Equation 13 (`eq:penalty`), first line. -/
lemma atom_comb (lam : Fin (n + 1) → ℝ) :
    ∑ k, lam k • P.atom k =
      Fin.cons (α := fun _ ↦ ℝ) ((P.N : ℝ) * P.gcomb lam) (fun i ↦ (P.N : ℝ) ^ 2 * P.acomb lam i) := by
  funext r
  induction r using Fin.cases with
  | zero =>
    simp only [Finset.sum_apply, Pi.smul_apply, atom, Fin.cons_zero, smul_eq_mul, gcomb,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  | succ i =>
    simp only [Finset.sum_apply, Pi.smul_apply, atom, Fin.cons_succ, smul_eq_mul, acomb,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring

@[simp] lemma alpha_castSucc (k : Fin n) (i : Fin m) :
    P.alpha (Fin.castSucc k) i = (P.A i k : ℝ) - (P.b i : ℝ) / P.T := by
  simp [alpha]

@[simp] lemma alpha_last (i : Fin m) : P.alpha (Fin.last n) i = -(P.b i : ℝ) / P.T := by
  simp [alpha]

@[simp] lemma gamma_castSucc (k : Fin n) : P.gamma (Fin.castSucc k) = P.C + P.c k := by
  simp [gamma]

@[simp] lemma gamma_last : P.gamma (Fin.last n) = P.C := by
  simp [gamma]

lemma T_pos : (0 : ℝ) < P.T := by exact_mod_cast P.one_le_T

lemma acomb_snoc (x : Fin n → ℝ) (t : ℝ) (i : Fin m) :
    P.acomb (Fin.snoc (α := fun _ ↦ ℝ) x t) i =
      (P.toLP.A *ᵥ x) i - (∑ k, x k + t) * (P.b i : ℝ) / P.T := by
  simp only [acomb, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, alpha_castSucc,
    alpha_last]
  have h1 : ∑ k, x k * ((P.A i k : ℝ) - (P.b i : ℝ) / P.T) =
      (P.toLP.A *ᵥ x) i - (∑ k, x k) * (P.b i : ℝ) / P.T := by
    simp only [mulVec, dotProduct, toLP_A, Finset.sum_mul, Finset.sum_div,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [h1]; ring

lemma gcomb_snoc (x : Fin n → ℝ) (t : ℝ) :
    P.gcomb (Fin.snoc (α := fun _ ↦ ℝ) x t) = (P.C : ℝ) * (∑ k, x k + t) + P.toLP.c ⬝ᵥ x := by
  simp only [gcomb, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, gamma_castSucc,
    gamma_last]
  have h1 : ∑ k, x k * ((P.C + P.c k : ℤ) : ℝ) = (P.C : ℝ) * ∑ k, x k + P.toLP.c ⬝ᵥ x := by
    simp only [dotProduct, toLP_c, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by push_cast; ring
  rw [h1]; ring

lemma acomb_sub (a b : Fin (n + 1) → ℝ) : P.acomb (a - b) = P.acomb a - P.acomb b := by
  funext i; simp [acomb, sub_mul, Finset.sum_sub_distrib]

lemma acomb_add (a b : Fin (n + 1) → ℝ) : P.acomb (a + b) = P.acomb a + P.acomb b := by
  funext i; simp [acomb, add_mul, Finset.sum_add_distrib]

lemma acomb_smul (r : ℝ) (a : Fin (n + 1) → ℝ) : P.acomb (r • a) = r • P.acomb a := by
  funext i; simp [acomb, Finset.mul_sum, mul_assoc]

lemma gcomb_sub (a b : Fin (n + 1) → ℝ) : P.gcomb (a - b) = P.gcomb a - P.gcomb b := by
  simp [gcomb, sub_mul, Finset.sum_sub_distrib]

lemma gcomb_add (a b : Fin (n + 1) → ℝ) : P.gcomb (a + b) = P.gcomb a + P.gcomb b := by
  simp [gcomb, add_mul, Finset.sum_add_distrib]

lemma gcomb_smul (r : ℝ) (a : Fin (n + 1) → ℝ) : P.gcomb (r • a) = r * P.gcomb a := by
  simp [gcomb, Finset.mul_sum, mul_assoc]

omit P in
lemma sum_eq_sum_univ_of {M : Type*} [AddCommMonoid M] (S : Finset (Fin (n + 1)))
    (f : Fin (n + 1) → M) (hf : ∀ k ∉ S, f k = 0) : ∑ k ∈ S, f k = ∑ k, f k :=
  Finset.sum_subset (subset_univ _) (fun k _ hk ↦ hf k hk)

/-! ### The quantities of the basis `B̂` (formulas of Lemma 2 (`lem:hom`)) -/

variable (B : Finset (Fin n))

/-- `x^B` -/
noncomputable def xB : Fin n → ℝ := P.toLP.basicSol B
/-- `y^B = v^{B̂}` -/
noncomputable def yB : Fin m → ℝ := P.toLP.dualVec B

/-- `λ^{B̂} = (x^B, T - 1ᵀx^B)/T` (Lemma 2 (`lem:hom`)(a)). -/
noncomputable def lamHat : Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ ↦ ℝ) (fun k ↦ P.xB B k / P.T) ((P.T - ∑ k, P.xB B k) / P.T)

/-- `h^{B̂} = C + (y^B)ᵀb/T` (Lemma 2 (`lem:hom`)(b)). -/
noncomputable def hHat : ℝ := P.C + (P.yB B ⬝ᵥ fun i ↦ (P.b i : ℝ)) / P.T

/-- `u` with `A u = y^B`, vanishing off `B`. -/
noncomputable def u0 : Fin n → ℝ := P.toLP.solOn B (P.yB B)

/-- `u^{B̂} = M_{B̂}⁻¹ (v, 0)ᵀ` (Equation 15 (`eq:projection-quantities`)). -/
noncomputable def uHat : Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ ↦ ℝ) (P.u0 B) (-∑ k, P.u0 B k)

/-- `‖y^B‖²` -/
noncomputable def ySq : ℝ := P.yB B ⬝ᵥ P.yB B

/-- `ε^{B̂} = h/(N² + ‖v‖²)` (Equation 15 (`eq:projection-quantities`)). -/
noncomputable def eps : ℝ := P.hHat B / ((P.N : ℝ) ^ 2 + P.ySq B)

/-- `λ^{*B̂} = λ^{B̂} - ε u` (Lemma 4 (`lem:corral`)(a)). -/
noncomputable def lamStar : Fin (n + 1) → ℝ := P.lamHat B - P.eps B • P.uHat B

/-- `w_{B̂} = (N s, -N² ε v)` with `s = N² ε` (Lemma 4 (`lem:corral`)(a)). -/
noncomputable def wHat : Fin (m + 1) → ℝ :=
  Fin.cons (α := fun _ ↦ ℝ) ((P.N : ℝ) * ((P.N : ℝ) ^ 2 * P.eps B))
    (fun i ↦ -((P.N : ℝ) ^ 2 * P.eps B) * P.yB B i)

/-- The reduced costs of `B̂`: `c̄^B` on the original labels, `0` on the slack label
(Lemma 2 (`lem:hom`)(c)). -/
noncomputable def rcHat : Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ ↦ ℝ) (P.toLP.reducedCost B) 0

/-- `d^{B̂,j} = (d^{B,j}, -1ᵀd^{B,j})`. -/
noncomputable def dirHat (j : Fin n) : Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ ↦ ℝ) (P.toLP.basicDir B j) (-∑ k, P.toLP.basicDir B j k)

variable {P B}

lemma lamHat_eq_zero (hB : P.toLP.IsBasis B) : ∀ k ∉ hat B, P.lamHat B k = 0 :=
  snoc_eq_zero_of_not_mem_hat fun k hk ↦ by
    simp [xB, hB.basicSol_spec.2 k hk]

lemma uHat_eq_zero (hB : P.toLP.IsBasis B) : ∀ k ∉ hat B, P.uHat B k = 0 :=
  snoc_eq_zero_of_not_mem_hat fun k hk ↦ (hB.solOn_spec _).2 k hk

lemma lamStar_eq_zero (hB : P.toLP.IsBasis B) : ∀ k ∉ hat B, P.lamStar B k = 0 := by
  intro k hk; simp [lamStar, lamHat_eq_zero hB k hk, uHat_eq_zero hB k hk]

lemma sum_lamHat : ∑ k, P.lamHat B k = 1 := by
  rw [lamHat, sum_snoc, ← Finset.sum_div]
  field_simp [P.T_pos.ne']
  ring

lemma sum_uHat : ∑ k, P.uHat B k = 0 := by
  rw [uHat, sum_snoc]; ring

lemma sum_lamStar : ∑ k, P.lamStar B k = 1 := by
  simp [lamStar, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_lamHat, sum_uHat]

lemma mulVec_div (x : Fin n → ℝ) (r : ℝ) :
    P.toLP.A *ᵥ (fun k ↦ x k / r) = fun i ↦ (P.toLP.A *ᵥ x) i / r := by
  funext i; simp [mulVec, dotProduct, Finset.sum_div, mul_div_assoc]

lemma acomb_lamHat (hB : P.toLP.IsBasis B) : P.acomb (P.lamHat B) = 0 := by
  funext i
  rw [lamHat, acomb_snoc, mulVec_div, ← Finset.sum_div]
  have h := congrFun hB.basicSol_spec.1 i
  simp only [xB, h, toLP_b, Pi.zero_apply]
  field_simp [P.T_pos.ne']
  ring

lemma acomb_uHat (hB : P.toLP.IsBasis B) : P.acomb (P.uHat B) = P.yB B := by
  funext i
  rw [uHat, acomb_snoc, u0, (hB.solOn_spec _).1]
  ring

lemma gcomb_lamHat (hB : P.toLP.IsBasis B) : P.gcomb (P.lamHat B) = P.hHat B := by
  rw [lamHat, gcomb_snoc, hHat]
  have h1 : P.toLP.c ⬝ᵥ (fun k ↦ P.xB B k / P.T) = (P.toLP.c ⬝ᵥ P.xB B) / P.T := by
    simp [dotProduct, Finset.sum_div, mul_div_assoc]
  rw [h1, xB, hB.objValue_eq, ← Finset.sum_div]
  have : P.toLP.b = fun i ↦ (P.b i : ℝ) := rfl
  rw [this, yB]
  field_simp [P.T_pos.ne']
  ring

lemma gcomb_uHat (hB : P.toLP.IsBasis B) : P.gcomb (P.uHat B) = P.ySq B := by
  have h0 : ∑ k, P.toLP.reducedCost B k * P.u0 B k = 0 := by
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    by_cases hk : k ∈ B
    · simp [hB.reducedCost_of_mem hk]
    · simp [u0, (hB.solOn_spec _).2 k hk]
  rw [uHat, gcomb_snoc, hB.cost_eq, h0]
  rw [u0, (hB.solOn_spec _).1, ySq, yB]
  ring

lemma acomb_lamStar (hB : P.toLP.IsBasis B) :
    P.acomb (P.lamStar B) = -(P.eps B) • P.yB B := by
  rw [lamStar, acomb_sub, acomb_smul, acomb_lamHat hB, acomb_uHat hB]
  simp

lemma gcomb_lamStar (hB : P.toLP.IsBasis B) :
    P.gcomb (P.lamStar B) = P.hHat B - P.eps B * P.ySq B := by
  rw [lamStar, gcomb_sub, gcomb_smul, gcomb_lamHat hB, gcomb_uHat hB]

lemma ySq_nonneg : 0 ≤ P.ySq B := by
  unfold ySq; exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _

lemma N_pos' (hm : 1 ≤ m) : (0 : ℝ) < P.N := by exact_mod_cast P.N_pos hm

lemma denom_pos (hm : 1 ≤ m) : 0 < (P.N : ℝ) ^ 2 + P.ySq B := by
  have := P.N_pos' hm
  have := P.ySq_nonneg (B := B)
  positivity

/-- `ε (N² + ‖v‖²) = h`. -/
lemma eps_mul_denom (hm : 1 ≤ m) : P.eps B * ((P.N : ℝ) ^ 2 + P.ySq B) = P.hHat B := by
  rw [eps, div_mul_cancel₀ _ (P.denom_pos hm).ne']

/-- `s = N² ε = h - ε ‖v‖²`. -/
lemma hHat_sub (hm : 1 ≤ m) : P.hHat B - P.eps B * P.ySq B = (P.N : ℝ) ^ 2 * P.eps B := by
  have := P.eps_mul_denom (B := B) hm
  linarith [this]

/-- `∑_k λ^{*}_k p_k = w_{B̂}` (Lemma 4 (`lem:corral`)(a), via Equation 13 (`eq:penalty`)). -/
lemma comb_lamStar (hB : P.toLP.IsBasis B) (hm : 1 ≤ m) :
    ∑ k, P.lamStar B k • P.atom k = P.wHat B := by
  rw [atom_comb, gcomb_lamStar hB, acomb_lamStar hB, hHat_sub hm, wHat]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- `γ_k - α_kᵀ v - h = c̄_k` (the reduced costs of `B̂`, Lemma 2 (`lem:hom`)(c)). -/
lemma gamma_sub_eq_rcHat (k : Fin (n + 1)) :
    (P.gamma k : ℝ) - ∑ i, P.alpha k i * P.yB B i - P.hHat B = P.rcHat B k := by
  induction k using Fin.lastCases with
  | last =>
    simp only [gamma_last, alpha_last, rcHat, Fin.snoc_last, hHat, dotProduct]
    rw [Finset.sum_div]
    have : ∑ i, -(P.b i : ℝ) / P.T * P.yB B i = -∑ i, P.yB B i * P.b i / P.T := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [this]; ring
  | cast k =>
    simp only [gamma_castSucc, alpha_castSucc, rcHat, Fin.snoc_castSucc, hHat, dotProduct,
      LP.reducedCost, toLP_c, toLP_col, Int.cast_add]
    rw [Finset.sum_div]
    have : ∑ i, ((P.A i k : ℝ) - P.b i / P.T) * P.yB B i =
        ∑ i, P.yB B i * P.A i k - ∑ i, P.yB B i * P.b i / P.T := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [this, yB]; ring

/-- Lemma 4 (`lem:corral`)(b): `g_k(w_{B̂}) = N² s c̄_k = N⁴ ε c̄_k`. -/
lemma gap_wHat (hm : 1 ≤ m) (k : Fin (n + 1)) :
    gap P.atom k (P.wHat B) = (P.N : ℝ) ^ 4 * P.eps B * P.rcHat B k := by
  rw [← gamma_sub_eq_rcHat]
  have hden := P.eps_mul_denom (B := B) hm
  simp only [gap, normSq, dotProduct, Fin.sum_univ_succ, atom, wHat, Fin.cons_zero,
    Fin.cons_succ]
  have e1 : ∑ i, (P.N : ℝ) ^ 2 * P.alpha k i * (-((P.N : ℝ) ^ 2 * P.eps B) * P.yB B i) =
      -((P.N : ℝ) ^ 4 * P.eps B) * ∑ i, P.alpha k i * P.yB B i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  have e2 : ∑ i, (-((P.N : ℝ) ^ 2 * P.eps B) * P.yB B i) *
      (-((P.N : ℝ) ^ 2 * P.eps B) * P.yB B i) = ((P.N : ℝ) ^ 2 * P.eps B) ^ 2 * P.ySq B := by
    rw [ySq, dotProduct, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [e1, e2]
  have : P.hHat B = P.eps B * ((P.N : ℝ) ^ 2 + P.ySq B) := hden.symm
  rw [this]; ring

lemma rcHat_eq_zero_of_mem (hB : P.toLP.IsBasis B) {k : Fin (n + 1)} (hk : k ∈ hat B) :
    P.rcHat B k = 0 := by
  induction k using Fin.lastCases with
  | last => simp [rcHat]
  | cast k => simp [rcHat, hB.reducedCost_of_mem (castSucc_mem_hat.1 hk)]

/-- Vectors vanishing off `B̂` with zero violation and zero sum are zero (the columns
of `M_{B̂}` are linearly independent). -/
lemma eq_zero_of_acomb (hB : P.toLP.IsBasis B) {β : Fin (n + 1) → ℝ}
    (hβ : ∀ k ∉ hat B, β k = 0) (hac : P.acomb β = 0) (hsum : ∑ k, β k = 0) : β = 0 := by
  have hsnoc : (Fin.snoc (α := fun _ ↦ ℝ) (fun k ↦ β (Fin.castSucc k)) (β (Fin.last n))) = β :=
    Fin.snoc_init_self β
  have hsum' : ∑ k, β (Fin.castSucc k) + β (Fin.last n) = 0 := by
    rw [← hsum, Fin.sum_univ_castSucc]
  have hA : P.toLP.A *ᵥ (fun k ↦ β (Fin.castSucc k)) = 0 := by
    funext i
    have := congrFun hac i
    rw [← hsnoc, acomb_snoc, hsum'] at this
    simpa using this
  have hx := hB.eq_zero (fun k hk ↦ hβ _ (by simpa using hk)) hA
  have hlast : β (Fin.last n) = 0 := by
    rw [hx] at hsum'; simpa using hsum'
  rw [← hsnoc, hx, hlast]
  funext k
  induction k using Fin.lastCases <;> simp

/-- Lemma 4 (`lem:corral`)(a), first claim: the atoms of `B̂` are affinely independent. -/
lemma affIndep_hat (hB : P.toLP.IsBasis B) (hm : 1 ≤ m) :
    IsAffinelyIndependent P.atom (hat B) := by
  intro β hcomb hsum i hi
  classical
  set β' : Fin (n + 1) → ℝ := fun k ↦ if k ∈ hat B then β k else 0 with hβ'
  have h0 : ∀ k ∉ hat B, β' k = 0 := fun k hk ↦ by simp [β', hk]
  have hc : ∑ k, β' k • P.atom k = 0 := by
    rw [← sum_eq_sum_univ_of (hat B) _ (fun k hk ↦ by simp [h0 k hk]), ← hcomb]
    exact Finset.sum_congr rfl fun k hk ↦ by simp [β', hk]
  have hs : ∑ k, β' k = 0 := by
    rw [← sum_eq_sum_univ_of (hat B) _ h0, ← hsum]
    exact Finset.sum_congr rfl fun k hk ↦ by simp [β', hk]
  have hac : P.acomb β' = 0 := by
    rw [atom_comb] at hc
    funext r
    have := congrFun hc r.succ
    simp only [Fin.cons_succ, Pi.zero_apply] at this
    have hN := (P.N_pos' hm).ne'
    simpa [hN] using this
  have := congrFun (eq_zero_of_acomb hB h0 hac hs) i
  simpa [β', hi] using this

lemma wHat_mem_affineHull (hB : P.toLP.IsBasis B) (hm : 1 ≤ m) :
    P.wHat B ∈ affineHull P.atom (hat B) := by
  refine ⟨P.lamStar B, ?_, ?_⟩
  · rw [sum_eq_sum_univ_of _ _ (lamStar_eq_zero hB), sum_lamStar]
  · rw [sum_eq_sum_univ_of _ _ (fun k hk ↦ by simp [lamStar_eq_zero hB k hk]),
      comb_lamStar hB hm]

/-- Lemma 4 (`lem:corral`)(a): `w_{B̂} = wHat`. -/
lemma affineMin_hat (hB : P.toLP.IsBasis B) (hm : 1 ≤ m) :
    affineMin P.atom (hat B) = P.wHat B := by
  apply affineMin_eq_of_gap_zero _ (wHat_mem_affineHull hB hm)
  intro i hi
  rw [gap_wHat hm, rcHat_eq_zero_of_mem hB hi, mul_zero]

/-- Lemma 4 (`lem:corral`)(a): `λ^{*B̂} = lamStar`. -/
lemma affineCoeffs_hat (hB : P.toLP.IsBasis B) (hm : 1 ≤ m) :
    affineCoeffs P.atom (hat B) = P.lamStar B := by
  apply affineCoeffs_eq_of _ (affIndep_hat hB hm) (lamStar_eq_zero hB)
  · rw [sum_eq_sum_univ_of _ _ (lamStar_eq_zero hB), sum_lamStar]
  · rw [affineMin_hat hB hm, sum_eq_sum_univ_of _ _ (fun k hk ↦ by simp [lamStar_eq_zero hB k hk]),
      comb_lamStar hB hm]

/-! ### Bounds via Cramer's rule (proofs of Lemma 8 (`lem:T-bound`) and Lemma 5
(`lem:bases-corrals`)) -/

omit P in
lemma sum_subtype_eq {M : Type*} [AddCommMonoid M] (S : Finset (Fin (n + 1)))
    {f : Fin (n + 1) → M} (hf : ∀ k ∉ S, f k = 0) :
    ∑ c : {k // k ∈ S}, f c = ∑ k, f k := by
  rw [Finset.sum_coe_sort S f]; exact sum_eq_sum_univ_of S f hf

omit P in
lemma sum_subtype_eq' {M : Type*} [AddCommMonoid M] (S : Finset (Fin n))
    {f : Fin n → M} (hf : ∀ k ∉ S, f k = 0) :
    ∑ c : {k // k ∈ S}, f c = ∑ k, f k := by
  rw [Finset.sum_coe_sort S f]
  exact Finset.sum_subset (subset_univ _) (fun k _ hk ↦ hf k hk)

/-- Lemma 8 (`lem:T-bound`) at basic solutions: every coordinate of `x^B` has absolute value
at most `m! U^m`. -/
lemma abs_xB_le (hB : P.toLP.IsBasis B) (k : Fin n) :
    |P.xB B k| ≤ ((m.factorial * P.U ^ m : ℕ) : ℝ) := by
  classical
  by_cases hk : k ∈ B
  swap
  · rw [xB, hB.basicSol_spec.2 k hk, abs_zero]; positivity
  have hcard : Fintype.card {k // k ∈ B} = Fintype.card (Fin m) := by
    simp [hB.1]
  have hinj : ∀ z : {k // k ∈ B} → ℝ,
      (∀ i, ∑ c : {k // k ∈ B}, ((P.A i c : ℤ) : ℝ) * z c = 0) → z = 0 := by
    intro z hz
    set x : Fin n → ℝ := fun k ↦ if h : k ∈ B then z ⟨k, h⟩ else 0
    have hx0 : ∀ k ∉ B, x k = 0 := fun k hk ↦ by simp [x, hk]
    have hAx : P.toLP.A *ᵥ x = 0 := by
      funext i
      have e : (P.toLP.A *ᵥ x) i = ∑ c : {k // k ∈ B}, ((P.A i c : ℤ) : ℝ) * z c := by
        simp only [mulVec, dotProduct, toLP_A]
        rw [← sum_subtype_eq' B (f := fun k ↦ (P.A i k : ℝ) * x k) (fun k hk ↦ by simp [hx0 k hk])]
        exact Finset.sum_congr rfl fun c _ ↦ by simp [x, c.2]
      rw [e, hz i]; rfl
    have := hB.eq_zero hx0 hAx
    funext c
    have := congrFun this c
    simpa [x, c.2] using this
  have hsys : ∀ i, ∑ c : {k // k ∈ B}, ((P.A i c : ℤ) : ℝ) * P.xB B c = (P.b i : ℝ) := by
    intro i
    have h := congrFun hB.basicSol_spec.1 i
    simp only [mulVec, dotProduct, toLP_A, toLP_b] at h
    rw [← h, sum_subtype_eq' B (f := fun k ↦ (P.A i k : ℝ) * P.xB B k)
      (fun k hk ↦ by simp [xB, hB.basicSol_spec.2 k hk])]
    rfl
  have := (int_system_bound hcard (fun i (c : {k // k ∈ B}) ↦ P.A i c) hinj P.U
    (fun i c ↦ P.abs_A_le i c) P.b P.abs_b_le (fun c ↦ P.xB B c) hsys ⟨k, hk⟩).1
  simpa using this

/-- Lemma 8 (`lem:T-bound`) at basic solutions: `2 · 1ᵀx^B < T`. -/
lemma two_mul_sum_xB_lt (hB : P.toLP.IsBasis B) : 2 * ∑ k, P.xB B k < P.T := by
  have hsum : ∑ k, P.xB B k ≤ m * ((m.factorial * P.U ^ m : ℕ) : ℝ) := by
    have hs : ∑ k, P.xB B k = ∑ k ∈ B, P.xB B k :=
      (Finset.sum_subset (subset_univ B) (fun k _ hk ↦ by simp [xB, hB.basicSol_spec.2 k hk])).symm
    rw [hs]
    calc ∑ k ∈ B, P.xB B k ≤ ∑ k ∈ B, ((m.factorial * P.U ^ m : ℕ) : ℝ) :=
          Finset.sum_le_sum fun k _ ↦ (le_abs_self _).trans (abs_xB_le hB k)
      _ = m * ((m.factorial * P.U ^ m : ℕ) : ℝ) := by simp [hB.1]
  have := P.two_mul_factorial_lt_T
  have h' : ((2 * m * (m.factorial * P.U ^ m) : ℕ) : ℝ) < P.T := by exact_mod_cast this
  push_cast at h' hsum
  linarith

lemma lamHat_nonneg (hB : P.toLP.IsFeasibleBasis B) (k : Fin (n + 1)) : 0 ≤ P.lamHat B k := by
  induction k using Fin.lastCases with
  | last =>
    simp only [lamHat, Fin.snoc_last]
    have := two_mul_sum_xB_lt hB.1
    have h0 : 0 ≤ ∑ k, P.xB B k := Finset.sum_nonneg fun k _ ↦ hB.2 k
    apply div_nonneg _ P.T_pos.le
    linarith
  | cast k =>
    simp only [lamHat, Fin.snoc_castSucc]
    exact div_nonneg (hB.2 k) P.T_pos.le

/-- Lemma 9 (`lem:induced-facts`)(b): `h^{B̂} ≥ 1` for a feasible basis. -/
lemma one_le_hHat (hB : P.toLP.IsFeasibleBasis B) : 1 ≤ P.hHat B := by
  rw [← gcomb_lamHat hB.1, ← sum_lamHat (P := P) (B := B), gcomb]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  have hg : (1 : ℝ) ≤ P.gamma k := by exact_mod_cast P.one_le_gamma k
  nlinarith [lamHat_nonneg hB k]

lemma eps_pos (hB : P.toLP.IsFeasibleBasis B) (hm : 1 ≤ m) : 0 < P.eps B := by
  rw [eps]
  exact div_pos (by linarith [one_le_hHat hB]) (P.denom_pos hm)

variable (P B) in
/-- The integer matrix `M̃_{B̂}`: the columns `(T α_k, 1)ᵀ` for `k ∈ B̂`. -/
def Qt : Matrix (Fin (m + 1)) {k // k ∈ hat B} ℤ :=
  fun r c ↦ Fin.snoc (α := fun _ ↦ ℤ) (P.scaledAlpha c) 1 r

lemma sum_Qfull (β : Fin (n + 1) → ℝ) (r : Fin (m + 1)) :
    ∑ k, ((Fin.snoc (α := fun _ ↦ ℤ) (P.scaledAlpha k) 1 r : ℤ) : ℝ) * β k =
      Fin.snoc (α := fun _ ↦ ℝ) (fun i ↦ (P.T : ℝ) * P.acomb β i) (∑ k, β k) r := by
  induction r using Fin.lastCases with
  | last => simp
  | cast i =>
    simp only [Fin.snoc_castSucc, acomb, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [← P.T_mul_alpha]; ring

lemma Qt_sum {β : Fin (n + 1) → ℝ} (hβ : ∀ k ∉ hat B, β k = 0) (r : Fin (m + 1)) :
    ∑ c, (P.Qt B r c : ℝ) * β c =
      Fin.snoc (α := fun _ ↦ ℝ) (fun i ↦ (P.T : ℝ) * P.acomb β i) (∑ k, β k) r := by
  rw [← sum_Qfull β r]
  exact sum_subtype_eq (hat B) (f := fun k ↦
    ((Fin.snoc (α := fun _ ↦ ℤ) (P.scaledAlpha k) 1 r : ℤ) : ℝ) * β k)
    (fun k hk ↦ by simp [hβ k hk])

lemma card_hat_subtype (hB : P.toLP.IsBasis B) :
    Fintype.card {k // k ∈ hat B} = Fintype.card (Fin (m + 1)) := by
  simp [card_hat, hB.1]

lemma Qt_inj (hB : P.toLP.IsBasis B) :
    ∀ z : {k // k ∈ hat B} → ℝ, (∀ r, ∑ c, (P.Qt B r c : ℝ) * z c = 0) → z = 0 := by
  classical
  intro z hz
  set β : Fin (n + 1) → ℝ := fun k ↦ if h : k ∈ hat B then z ⟨k, h⟩ else 0
  have hβ : ∀ k ∉ hat B, β k = 0 := fun k hk ↦ by simp [β, hk]
  have hz' : ∀ r, Fin.snoc (α := fun _ ↦ ℝ) (fun i ↦ (P.T : ℝ) * P.acomb β i) (∑ k, β k) r = 0 := by
    intro r
    rw [← Qt_sum hβ r, ← hz r]
    exact Finset.sum_congr rfl fun c _ ↦ by simp [β, c.2]
  have hac : P.acomb β = 0 := by
    funext i
    have := hz' (Fin.castSucc i)
    simp only [Fin.snoc_castSucc] at this
    simpa [P.T_pos.ne'] using this
  have hs : ∑ k, β k = 0 := by simpa using hz' (Fin.last m)
  have := eq_zero_of_acomb hB hβ hac hs
  funext c
  have := congrFun this c
  simpa [β, c.2] using this

lemma Qt_le (r : Fin (m + 1)) (c : {k // k ∈ hat B}) : |P.Qt B r c| ≤ ((P.K : ℕ) : ℤ) := by
  induction r using Fin.lastCases with
  | last => simp [Qt]; exact_mod_cast P.one_le_K
  | cast i => simpa [Qt] using P.abs_scaledAlpha_le c i

lemma Hc_le_H : (((Fintype.card (Fin (m + 1))).factorial * P.K ^ Fintype.card (Fin (m + 1)) : ℕ) : ℝ)
    ≤ P.H := by
  simp only [Fintype.card_fin]; exact_mod_cast P.factorial_mul_K_pow_le_H

lemma Hc_pos : (0 : ℝ) <
    (((Fintype.card (Fin (m + 1))).factorial * P.K ^ Fintype.card (Fin (m + 1)) : ℕ) : ℝ) := by
  have := P.one_le_K
  have : 0 < (Fintype.card (Fin (m + 1))).factorial * P.K ^ Fintype.card (Fin (m + 1)) :=
    Nat.mul_pos (Nat.factorial_pos _) (pow_pos (by omega) _)
  exact_mod_cast this

lemma H_pos : (0 : ℝ) < P.H := by exact_mod_cast P.one_le_H

/-- Equation 23 (`eq:det-bound`) for a solution `β` (vanishing off `B̂`) of `M̃_{B̂} β = r`. -/
lemma Qt_bound (hB : P.toLP.IsBasis B) (r : Fin (m + 1) → ℤ) (hr : ∀ i, |r i| ≤ P.K)
    {β : Fin (n + 1) → ℝ} (hβ : ∀ k ∉ hat B, β k = 0)
    (hsys : ∀ i, Fin.snoc (α := fun _ ↦ ℝ) (fun i ↦ (P.T : ℝ) * P.acomb β i) (∑ k, β k) i = r i)
    {k : Fin (n + 1)} (hk : k ∈ hat B) :
    |β k| ≤ P.H ∧ (β k ≠ 0 → 1 / (P.H : ℝ) ≤ |β k|) := by
  have h := int_system_bound (card_hat_subtype hB) (P.Qt B) (Qt_inj hB) P.K (P.Qt_le) r hr
    (fun c ↦ β c) (fun i ↦ by rw [Qt_sum hβ i, hsys i]) ⟨k, hk⟩
  refine ⟨h.1.trans P.Hc_le_H, fun hne ↦ le_trans ?_ (h.2 hne)⟩
  exact one_div_le_one_div_of_le P.Hc_pos P.Hc_le_H

/-- Lemma 5 (`lem:bases-corrals`)(a): `λ^{B̂}_k ≥ 1/H` on `B̂`. -/
lemma lamHat_ge (hB : P.toLP.IsFeasibleBasis B) (hnd : P.toLP.IsNondegenerate B)
    {k : Fin (n + 1)} (hk : k ∈ hat B) : 1 / (P.H : ℝ) ≤ P.lamHat B k := by
  have hpos : 0 < P.lamHat B k := by
    induction k using Fin.lastCases with
    | last =>
      simp only [lamHat, Fin.snoc_last]
      have := two_mul_sum_xB_lt hB.1
      have h0 : 0 ≤ ∑ k, P.xB B k := Finset.sum_nonneg fun k _ ↦ hB.2 k
      apply div_pos _ P.T_pos
      linarith
    | cast k =>
      simp only [lamHat, Fin.snoc_castSucc]
      exact div_pos (hnd k (castSucc_mem_hat.1 hk)) P.T_pos
  have := (Qt_bound hB.1 (Fin.snoc (α := fun _ ↦ ℤ) 0 1) (fun i ↦ by
      induction i using Fin.lastCases with
      | last => simp; exact_mod_cast P.one_le_K
      | cast i => simp) (lamHat_eq_zero hB.1) (fun i ↦ by
      induction i using Fin.lastCases with
      | last => simp [sum_lamHat]
      | cast i => simp [acomb_lamHat hB.1]) hk).2 hpos.ne'
  rwa [abs_of_pos hpos] at this

/-- Lemma 5 (`lem:bases-corrals`)(b): bounds for the basic direction `d^{B̂,j}`. -/
lemma dirHat_bound (hB : P.toLP.IsBasis B) {j : Fin n} (hj : j ∉ B)
    {k : Fin (n + 1)} (hk : k ∈ hat B) :
    |P.dirHat B j k| ≤ P.H ∧ (P.dirHat B j k ≠ 0 → 1 / (P.H : ℝ) ≤ |P.dirHat B j k|) := by
  classical
  have hdir := hB.basicDir_spec hj
  set D := P.dirHat B j
  set D' : Fin (n + 1) → ℝ := fun k ↦ if k = Fin.castSucc j then 0 else D k
  have hD'0 : ∀ k ∉ hat B, D' k = 0 := by
    intro k hk
    by_cases hkj : k = Fin.castSucc j
    · simp [D', hkj]
    · simp only [D', hkj, ite_false]
      exact snoc_eq_zero_of_not_mem_hat (B := insert j B) (fun l hl ↦ hdir.2.2 l
        (fun h ↦ hl (mem_insert_of_mem h)) (fun h ↦ hl (h ▸ mem_insert_self _ _)))
        k (by
          intro h
          induction k using Fin.lastCases with
          | last => exact hk last_mem_hat
          | cast k =>
            rw [castSucc_mem_hat, mem_insert] at h
            rcases h with h | h
            · exact hkj (by rw [h])
            · exact hk (castSucc_mem_hat.2 h))
  have hDD' : D' = D - Pi.single (Fin.castSucc j) 1 := by
    funext k
    by_cases hkj : k = Fin.castSucc j
    · subst hkj; simp [D', D, dirHat, hdir.2.1]
    · simp [D', hkj]
  have hacD : P.acomb D = 0 := by
    funext i; simp [D, dirHat, acomb_snoc, hdir.1]
  have hsD : ∑ k, D k = 0 := by simp [D, dirHat, sum_snoc]
  have hsingle : ∀ i, P.acomb (Pi.single (Fin.castSucc j) 1) i = P.alpha (Fin.castSucc j) i := by
    intro i; simp [acomb, Pi.single_apply]
  have h := Qt_bound hB (fun r ↦ -(Fin.snoc (α := fun _ ↦ ℤ) (P.scaledAlpha (Fin.castSucc j)) 1 r))
    (fun r ↦ by
      induction r using Fin.lastCases with
      | last => simp; exact_mod_cast P.one_le_K
      | cast i => simpa using P.abs_scaledAlpha_le _ i) hD'0 (fun r ↦ by
      rw [hDD', acomb_sub, hacD]
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, hsD]
      induction r using Fin.lastCases with
      | last => simp
      | cast i => simp [hsingle, ← P.T_mul_alpha]; ring) hk
  have hkj : k ≠ Fin.castSucc j := fun h ↦ hj (castSucc_mem_hat.1 (h ▸ hk))
  simpa [D', hkj] using h

/-- Bounds on the dual quantities from the transposed system
`M̃_{B̂}ᵀ (v/T, h) = γ_{B̂}`: `|y_i/T| ≤ H` and `|h| ≤ H`. -/
lemma dual_bound (hB : P.toLP.IsBasis B) :
    (∀ i, |P.yB B i / P.T| ≤ P.H) ∧ |P.hHat B| ≤ P.H := by
  set z : Fin (m + 1) → ℝ := Fin.snoc (α := fun _ ↦ ℝ) (fun i ↦ P.yB B i / P.T) (P.hHat B)
  have hsys : ∀ c : {k // k ∈ hat B}, ∑ r, (P.Qt B r c : ℝ) * z r = P.gamma c := by
    intro c
    have h := gamma_sub_eq_rcHat (P := P) (B := B) c
    rw [rcHat_eq_zero_of_mem hB c.2] at h
    simp only [Fin.sum_univ_castSucc, Qt, z, Fin.snoc_castSucc, Fin.snoc_last, Int.cast_one, one_mul]
    have : ∑ i, ((P.scaledAlpha c i : ℤ) : ℝ) * (P.yB B i / P.T) = ∑ i, P.alpha c i * P.yB B i := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← P.T_mul_alpha]; field_simp [P.T_pos.ne']
    rw [this]; linarith
  have hb := fun l ↦ int_system_bound_transpose (card_hat_subtype hB) (P.Qt B) (Qt_inj hB) P.K
    P.Qt_le (fun c ↦ P.gamma c) (fun c ↦ P.abs_gamma_le c) z hsys l
  refine ⟨fun i ↦ ?_, ?_⟩
  · have := (hb (Fin.castSucc i)).1
    simp only [z, Fin.snoc_castSucc] at this
    exact this.trans P.Hc_le_H
  · have := (hb (Fin.last m)).1
    simp only [z, Fin.snoc_last] at this
    exact this.trans P.Hc_le_H

/-- `‖u^{B̂}‖_∞ ≤ m T² H²` (proof of Lemma 5 (`lem:bases-corrals`)(c)). -/
lemma abs_uHat_le (hB : P.toLP.IsBasis B) (k : Fin (n + 1)) :
    |P.uHat B k| ≤ m * (P.T : ℝ) ^ 2 * (P.H : ℝ) ^ 2 := by
  classical
  have hHp := P.H_pos
  by_cases hk : k ∈ hat B
  swap
  · rw [uHat_eq_zero hB k hk, abs_zero]; positivity
  set r : Fin (m + 1) → ℝ := Fin.snoc (α := fun _ ↦ ℝ) (fun i ↦ (P.T : ℝ) * P.yB B i) 0
  have h := real_system_bound (card_hat_subtype hB) (P.Qt B) (Qt_inj hB) P.K P.one_le_K
    P.Qt_le r (fun c ↦ P.uHat B c) (fun i ↦ by
      rw [Qt_sum (uHat_eq_zero hB) i, acomb_uHat hB, sum_uHat]) ⟨k, hk⟩
  have hr : ∑ i, |r i| ≤ m * ((P.T : ℝ) * ((P.T : ℝ) * P.H)) := by
    rw [Fin.sum_univ_castSucc]
    simp only [r, Fin.snoc_castSucc, Fin.snoc_last, abs_zero, add_zero]
    calc ∑ i : Fin m, |(P.T : ℝ) * P.yB B i| ≤ ∑ i : Fin m, (P.T : ℝ) * ((P.T : ℝ) * P.H) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have := (dual_bound hB).1 i
          rw [abs_mul, abs_of_pos P.T_pos]
          rw [abs_div, abs_of_pos P.T_pos, div_le_iff₀ P.T_pos] at this
          exact mul_le_mul_of_nonneg_left (by linarith) P.T_pos.le
      _ = m * ((P.T : ℝ) * ((P.T : ℝ) * P.H)) := by simp
  calc |P.uHat B k| ≤ (∑ i, |r i|) * _ := h
    _ ≤ (m * ((P.T : ℝ) * ((P.T : ℝ) * P.H))) * P.H :=
        mul_le_mul hr P.Hc_le_H P.Hc_pos.le (by positivity)
    _ = m * (P.T : ℝ) ^ 2 * (P.H : ℝ) ^ 2 := by ring

/-- Lemma 5 (`lem:bases-corrals`)(c): `ε^{B̂} |u_k| ≤ 1/(4 m H³)`. -/
lemma eps_mul_abs_uHat_le (hB : P.toLP.IsFeasibleBasis B) (hm : 1 ≤ m) (k : Fin (n + 1)) :
    P.eps B * |P.uHat B k| ≤ 1 / (4 * m * (P.H : ℝ) ^ 3) := by
  have hHp := P.H_pos
  have hTp := P.T_pos
  have hNp := P.N_pos' hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have heps : P.eps B ≤ P.H / (P.N : ℝ) ^ 2 := by
    rw [eps]
    have h1 := one_le_hHat hB
    have h2 := (dual_bound hB.1).2
    rw [abs_of_pos (by linarith)] at h2
    calc P.hHat B / ((P.N : ℝ) ^ 2 + P.ySq B) ≤ P.hHat B / (P.N : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left (by linarith) (by positivity)
            (by linarith [P.ySq_nonneg (B := B)])
      _ ≤ P.H / (P.N : ℝ) ^ 2 := div_le_div_of_nonneg_right h2 (by positivity)
  have hN : (P.N : ℝ) = 2 * m * P.T * (P.H : ℝ) ^ 3 := by simp [N]
  calc P.eps B * |P.uHat B k| ≤ (P.H / (P.N : ℝ) ^ 2) * (m * (P.T : ℝ) ^ 2 * (P.H : ℝ) ^ 2) :=
        mul_le_mul heps (abs_uHat_le hB.1 k) (abs_nonneg _) (by positivity)
    _ = 1 / (4 * m * (P.H : ℝ) ^ 3) := by
        rw [hN]; field_simp; ring

/-- Lemma 5 (`lem:bases-corrals`): `λ^{*B̂}_k > 0` on `B̂`, with the explicit margin. -/
lemma lamStar_ge (hB : P.toLP.IsFeasibleBasis B) (hnd : P.toLP.IsNondegenerate B) (hm : 1 ≤ m)
    {k : Fin (n + 1)} (hk : k ∈ hat B) :
    1 / (P.H : ℝ) - 1 / (4 * m * (P.H : ℝ) ^ 3) ≤ P.lamStar B k := by
  have h1 := lamHat_ge hB hnd hk
  have h2 := eps_mul_abs_uHat_le hB hm k
  have h3 : P.eps B * P.uHat B k ≤ P.eps B * |P.uHat B k| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (eps_pos hB hm).le
  simp only [lamStar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

lemma margin_pos (hm : 1 ≤ m) : 0 < 1 / (P.H : ℝ) - 1 / (4 * m * (P.H : ℝ) ^ 3) := by
  have hH : (1 : ℝ) ≤ P.H := by exact_mod_cast P.one_le_H
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hHp : (0 : ℝ) < P.H := by linarith
  rw [sub_pos, div_lt_div_iff₀ (by positivity) hHp]
  have h3 : (P.H : ℝ) ≤ (P.H : ℝ) ^ 3 := le_self_pow₀ hH (by norm_num)
  have h4 : (P.H : ℝ) ^ 3 * 1 ≤ (P.H : ℝ) ^ 3 * m :=
    mul_le_mul_of_nonneg_left hmR (by positivity)
  nlinarith

/-- Lemma 5 (`lem:bases-corrals`): for a feasible basis `B`, the set `B̂` is a corral. -/
lemma isCorral_hat (hB : P.toLP.IsFeasibleBasis B) (hnd : P.toLP.IsNondegenerate B)
    (hm : 1 ≤ m) : IsCorral P.atom (hat B) := by
  refine ⟨⟨_, last_mem_hat⟩, affIndep_hat hB.1 hm, fun k hk ↦ ?_⟩
  rw [affineCoeffs_hat hB.1 hm]
  exact lt_of_lt_of_le (P.margin_pos hm) (lamStar_ge hB hnd hm hk)

end WolfeSimplex.IntLP
