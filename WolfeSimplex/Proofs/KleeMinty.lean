import WolfeSimplex.Defs.KleeMinty
import WolfeSimplex.Defs.Rules
import WolfeSimplex.Defs.Shield
import WolfeSimplex.Proofs.SimplexFacts

/-!
# The Klee–Minty cube (paper: Lemma 15 (`lem:km`))

Proofs about the Klee–Minty LP `kleeMinty n`.

## Notation used in the proofs

* For a vector `x` on the labels `Fin (2n)`, `X x j` is the value of `x_j` (label `2j`)
  and `S x j` is the value of `s_j` (label `2j+1`), both as functions on `ℕ`.
* `T Y i = ∑_{j<i} 10^{i-j} Y_j` (in the summary of the paper's argument,
  `T = 10 Z_{i-1}`). Row `i` of `A x` is `X_i + S_i + 2 T_i`.
* A vector `a : ℕ → Bool` describes the basis `basisA n a` that contains `x_i` if
  `a i = true` and `s_i` otherwise (only `a i` for `i < n` matter).
* `gV n a r u` is the solution of `A x = r` (row `i` has right-hand side `r i`)
  whose nonbasic variable of pair `i` (with respect to `basisA n a`) has the value
  `u i`. With `r = b, u = 0` this is the basic solution, with `r = 0, u = δ_k` the
  basic direction of the nonbasic label of pair `k`.
* `sg a k i = ∏_{k ≤ l < i} (-1)^{a l}`. The reduced cost of the nonbasic label of
  pair `k` is `-sg a k n · 10^{n-1-k}`.
* `v n a = ∑_{k<n, sg a k n = -1} 2^k` is the counter: each Dantzig/Bland pivot
  increases it by exactly one.
-/

namespace WolfeSimplex

namespace KM

open Finset Matrix

variable {n : ℕ}

/-- Shorthand for the Klee–Minty LP over `ℝ`. -/
abbrev P (n : ℕ) : LP n (2 * n) := (kleeMinty n).toLP

/-! ### Entries -/

/-- The entries of `A`, as a function of natural numbers. -/
def aent (i k : ℕ) : ℝ :=
  if k % 2 = 1 then (if k / 2 = i then 1 else 0)
  else if k / 2 = i then 1
  else if k / 2 < i then 2 * 10 ^ (i - k / 2)
  else 0

theorem A_apply (i : Fin n) (k : Fin (2 * n)) : (P n).A i k = aent i k := by
  simp only [P, IntLP.toLP, kleeMinty, Matrix.map_apply, Matrix.of_apply, aent]
  split_ifs <;> push_cast <;> rfl

theorem b_apply (i : Fin n) : (P n).b i = (100 : ℝ) ^ i.val := by
  simp [P, IntLP.toLP, kleeMinty]

theorem c_apply (k : Fin (2 * n)) :
    (P n).c k = if k.val % 2 = 0 then -(10 : ℝ) ^ (n - 1 - k.val / 2) else 0 := by
  simp only [P, IntLP.toLP, kleeMinty]
  split_ifs <;> push_cast <;> rfl

/-! ### Coordinates `X`, `S` and the sums `T` -/

/-- The vector `x`, extended by `0` to all natural numbers. -/
def ext (x : Fin (2 * n) → ℝ) (k : ℕ) : ℝ := if h : k < 2 * n then x ⟨k, h⟩ else 0

/-- The value of `x_j` (label `2j`). -/
def X (x : Fin (2 * n) → ℝ) (j : ℕ) : ℝ := ext x (2 * j)

/-- The value of `s_j` (label `2j+1`). -/
def S (x : Fin (2 * n) → ℝ) (j : ℕ) : ℝ := ext x (2 * j + 1)

/-- `T Y i = ∑_{j<i} 10^{i-j} Y_j`. -/
def T (Y : ℕ → ℝ) (i : ℕ) : ℝ := ∑ j ∈ range i, 10 ^ (i - j) * Y j

theorem ext_val (x : Fin (2 * n) → ℝ) (k : Fin (2 * n)) : ext x k.val = x k := by
  simp [ext, k.isLt]

theorem apply_eq (x : Fin (2 * n) → ℝ) (k : Fin (2 * n)) :
    x k = if k.val % 2 = 0 then X x (k.val / 2) else S x (k.val / 2) := by
  have hk := k.isLt
  unfold X S
  split_ifs with h
  · rw [show 2 * (k.val / 2) = k.val by omega, ext_val]
  · rw [show 2 * (k.val / 2) + 1 = k.val by omega, ext_val]

theorem T_zero (Y : ℕ → ℝ) : T Y 0 = 0 := by simp [T]

theorem T_succ (Y : ℕ → ℝ) (i : ℕ) : T Y (i + 1) = 10 * (Y i + T Y i) := by
  have h : ∑ j ∈ range i, (10 : ℝ) ^ (i + 1 - j) * Y j =
      10 * ∑ j ∈ range i, (10 : ℝ) ^ (i - j) * Y j := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj ↦ ?_
    rw [mem_range] at hj
    rw [show i + 1 - j = (i - j) + 1 by omega, pow_succ]
    ring
  rw [T, T, sum_range_succ, h, show i + 1 - i = 1 by omega]
  ring

theorem T_congr {Y Y' : ℕ → ℝ} {i : ℕ} (h : ∀ j < i, Y j = Y' j) : T Y i = T Y' i := by
  refine sum_congr rfl fun j hj ↦ ?_
  rw [h j (mem_range.1 hj)]

theorem T_eq_cost (Y : ℕ → ℝ) (n : ℕ) :
    10 * ∑ j ∈ range n, 10 ^ (n - 1 - j) * Y j = T Y n := by
  rw [T, mul_sum]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [mem_range] at hj
  rw [show n - j = (n - 1 - j) + 1 by omega, pow_succ]
  ring

theorem sum_range_two_mul (g : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range (2 * n), g k = ∑ j ∈ range n, (g (2 * j) + g (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

/-- Row `i` of `A x`: `x_i + s_i + 2 ∑_{j<i} 10^{i-j} x_j`. -/
theorem mulVec_apply (x : Fin (2 * n) → ℝ) (i : Fin n) :
    ((P n).A *ᵥ x) i = X x i + S x i + 2 * T (X x) i := by
  have h1 : ((P n).A *ᵥ x) i = ∑ k ∈ range (2 * n), aent i k * ext x k := by
    rw [mulVec, dotProduct, ← Fin.sum_univ_eq_sum_range (fun k ↦ aent i k * ext x k)]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [A_apply, ext_val]
  rw [h1, sum_range_two_mul]
  have h2 : ∀ j ∈ range n, aent i (2 * j) * ext x (2 * j) + aent i (2 * j + 1) * ext x (2 * j + 1)
      = (if j = i then X x j + S x j else 0) +
        (if j < i then 2 * (10 ^ (i.val - j) * X x j) else 0) := by
    intro j _
    have e1 : (2 * j) % 2 = 0 := by omega
    have e2 : (2 * j) / 2 = j := by omega
    have e3 : (2 * j + 1) % 2 = 1 := by omega
    have e4 : (2 * j + 1) / 2 = j := by omega
    simp only [aent, e1, e2, e3, e4, X, S]
    split_ifs <;> first | contradiction | omega | ring
  rw [sum_congr rfl h2, sum_add_distrib, sum_ite_eq', ite_eq_left (mem_range.2 i.isLt),
    ← sum_filter, T, mul_sum]
  have h3 : (range n).filter (fun j ↦ j < i.val) = range i.val := by
    ext j; simp only [mem_filter, mem_range]; have := i.isLt; omega
  rw [h3]

/-- The cost: `cᵀx = -∑_j 10^{n-1-j} x_j`. -/
theorem cost_apply (x : Fin (2 * n) → ℝ) :
    (P n).c ⬝ᵥ x = -∑ j ∈ range n, 10 ^ (n - 1 - j) * X x j := by
  have h1 : (P n).c ⬝ᵥ x = ∑ k ∈ range (2 * n),
      (if k % 2 = 0 then -(10 : ℝ) ^ (n - 1 - k / 2) else 0) * ext x k := by
    rw [dotProduct, ← Fin.sum_univ_eq_sum_range
      (fun k ↦ (if k % 2 = 0 then -(10 : ℝ) ^ (n - 1 - k / 2) else 0) * ext x k)]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [c_apply, ext_val]
  rw [h1, sum_range_two_mul, ← sum_neg_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  have e1 : (2 * j) % 2 = 0 := by omega
  have e2 : (2 * j) / 2 = j := by omega
  have e3 : (2 * j + 1) % 2 = 1 := by omega
  simp only [e1, e2, e3, X]
  simp

/-! ### The bases `basisA n a` -/

/-- The basic label of pair `i`: `x_i` (label `2i`) if `a i`, else `s_i` (label `2i+1`). -/
def vlab (a : ℕ → Bool) (i : Fin n) : Fin (2 * n) :=
  ⟨2 * i.val + (if a i then 0 else 1), by have := i.isLt; split_ifs <;> omega⟩

/-- The nonbasic label of pair `i`: `s_i` if `a i`, else `x_i`. -/
def wlab (a : ℕ → Bool) (i : Fin n) : Fin (2 * n) :=
  ⟨2 * i.val + (if a i then 1 else 0), by have := i.isLt; split_ifs <;> omega⟩

/-- The basis containing `x_i` if `a i` and `s_i` otherwise, for every `i < n`. -/
def basisA (n : ℕ) (a : ℕ → Bool) : Finset (Fin (2 * n)) := univ.image (vlab a)

theorem vlab_val (a : ℕ → Bool) (i : Fin n) :
    (vlab a i).val = 2 * i.val + (if a i then 0 else 1) := rfl

theorem wlab_val (a : ℕ → Bool) (i : Fin n) :
    (wlab a i).val = 2 * i.val + (if a i then 1 else 0) := rfl

theorem wlab_div (a : ℕ → Bool) (i : Fin n) : (wlab a i).val / 2 = i.val := by
  rw [wlab_val]; split_ifs <;> omega

theorem vlab_div (a : ℕ → Bool) (i : Fin n) : (vlab a i).val / 2 = i.val := by
  rw [vlab_val]; split_ifs <;> omega

theorem mem_basisA {a : ℕ → Bool} {k : Fin (2 * n)} :
    k ∈ basisA n a ↔ (k.val % 2 = 0 ↔ a (k.val / 2) = true) := by
  constructor
  · rintro hk
    obtain ⟨i, -, rfl⟩ := mem_image.1 hk
    rw [vlab_div, vlab_val]
    cases h : a i.val <;> simp only [Bool.false_eq_true, ↓reduceIte, iff_false,
      iff_true] <;> omega
  · intro h
    have hk := k.isLt
    refine mem_image.2 ⟨⟨k.val / 2, by omega⟩, mem_univ _, Fin.ext ?_⟩
    rw [vlab_val]
    cases h' : a (k.val / 2) <;> simp only [h', Bool.false_eq_true, iff_false, iff_true,
      ↓reduceIte] at h ⊢ <;> omega

theorem mem_basisA_x {a : ℕ → Bool} {i : ℕ} (hi : 2 * i < 2 * n) :
    (⟨2 * i, hi⟩ : Fin (2 * n)) ∈ basisA n a ↔ a i = true := by
  rw [mem_basisA]
  simp only [show 2 * i % 2 = 0 by omega, show 2 * i / 2 = i by omega, true_iff]

theorem mem_basisA_s {a : ℕ → Bool} {i : ℕ} (hi : 2 * i + 1 < 2 * n) :
    (⟨2 * i + 1, hi⟩ : Fin (2 * n)) ∈ basisA n a ↔ a i = false := by
  rw [mem_basisA]
  simp only [show (2 * i + 1) / 2 = i by omega]
  cases a i <;> simp

theorem vlab_mem (a : ℕ → Bool) (i : Fin n) : vlab a i ∈ basisA n a :=
  mem_image_of_mem _ (mem_univ _)

theorem wlab_not_mem (a : ℕ → Bool) (i : Fin n) : wlab a i ∉ basisA n a := by
  rw [mem_basisA, wlab_div, wlab_val]
  cases h : a i.val <;> simp only [Bool.false_eq_true, ↓reduceIte, iff_false,
      iff_true] <;> omega

theorem not_mem_basisA {a : ℕ → Bool} {k : Fin (2 * n)} (hk : k ∉ basisA n a) :
    k = wlab a ⟨k.val / 2, by have := k.isLt; omega⟩ := by
  rw [mem_basisA] at hk
  apply Fin.ext
  rw [wlab_val]
  cases h : a (k.val / 2) <;> simp only [h, Bool.false_eq_true, iff_false, iff_true,
    ↓reduceIte, not_not] at hk ⊢ <;> omega

theorem wlab_inj {a : ℕ → Bool} {i i' : Fin n} (h : wlab a i = wlab a i') : i = i' := by
  apply Fin.ext
  rw [← wlab_div a i, ← wlab_div a i', h]

theorem card_basisA (a : ℕ → Bool) : (basisA n a).card = n := by
  rw [basisA, card_image_of_injective, card_univ, Fintype.card_fin]
  intro i i' h
  apply Fin.ext
  rw [← vlab_div a i, ← vlab_div a i', h]

/-- A basis `basisA n a'` never contains both labels of a pair. -/
theorem not_both (a a' : ℕ → Bool) (i : Fin n) :
    ¬ (vlab a i ∈ basisA n a' ∧ wlab a i ∈ basisA n a') := by
  rintro ⟨h1, h2⟩
  rw [mem_basisA, vlab_div, vlab_val] at h1
  rw [mem_basisA, wlab_div, wlab_val] at h2
  cases h : a i.val <;> cases h' : a' i.val <;>
    simp only [h, h', Bool.false_eq_true, ↓reduceIte, iff_true,
      iff_false] at h1 h2 <;> omega

theorem basisA_congr {a a' : ℕ → Bool} (h : ∀ j < n, a j = a' j) :
    basisA n a = basisA n a' := by
  ext k
  have hk := k.isLt
  rw [mem_basisA, mem_basisA, h _ (by omega)]

/-! ### The general solution of `A x = r` adapted to `basisA n a` -/

/-- `gT a r u i = T_i` for the solution `gV n a r u`. -/
def gT (a : ℕ → Bool) (r u : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => 10 * ((if a i then r i - u i - 2 * gT a r u i else u i) + gT a r u i)

/-- The value of `x_i` in `gV n a r u`. -/
def gX (a : ℕ → Bool) (r u : ℕ → ℝ) (i : ℕ) : ℝ :=
  if a i then r i - u i - 2 * gT a r u i else u i

/-- The value of `s_i` in `gV n a r u`. -/
def gS (a : ℕ → Bool) (r u : ℕ → ℝ) (i : ℕ) : ℝ :=
  if a i then u i else r i - u i - 2 * gT a r u i

/-- The solution of `A x = r` whose nonbasic variable of pair `i` has the value `u i`. -/
def gV (n : ℕ) (a : ℕ → Bool) (r u : ℕ → ℝ) : Fin (2 * n) → ℝ :=
  fun k ↦ if k.val % 2 = 0 then gX a r u (k.val / 2) else gS a r u (k.val / 2)

theorem gT_zero (a : ℕ → Bool) (r u : ℕ → ℝ) : gT a r u 0 = 0 := rfl

theorem gT_succ (a : ℕ → Bool) (r u : ℕ → ℝ) (i : ℕ) :
    gT a r u (i + 1) = 10 * (gX a r u i + gT a r u i) := rfl

theorem T_gX (a : ℕ → Bool) (r u : ℕ → ℝ) (i : ℕ) : T (gX a r u) i = gT a r u i := by
  induction i with
  | zero => rw [T_zero, gT_zero]
  | succ i ih => rw [T_succ, gT_succ, ih]

theorem X_gV (a : ℕ → Bool) (r u : ℕ → ℝ) {j : ℕ} (hj : j < n) :
    X (gV n a r u) j = gX a r u j := by
  have h1 : 2 * j < 2 * n := by omega
  have h2 : 2 * j % 2 = 0 := by omega
  have h3 : 2 * j / 2 = j := by omega
  simp only [X, ext, gV, h1, dite_true, h2, h3, ↓reduceIte]

theorem S_gV (a : ℕ → Bool) (r u : ℕ → ℝ) {j : ℕ} (hj : j < n) :
    S (gV n a r u) j = gS a r u j := by
  have h1 : 2 * j + 1 < 2 * n := by omega
  have h2 : (2 * j + 1) % 2 = 1 := by omega
  have h3 : (2 * j + 1) / 2 = j := by omega
  simp only [S, ext, gV, h1, dite_true, h2, h3, one_ne_zero, ↓reduceIte]

theorem mulVec_gV (a : ℕ → Bool) (r u : ℕ → ℝ) :
    (P n).A *ᵥ gV n a r u = fun i : Fin n ↦ r i := by
  funext i
  rw [mulVec_apply, X_gV _ _ _ i.isLt, S_gV _ _ _ i.isLt,
    T_congr (Y' := gX a r u) (fun j hj ↦ X_gV _ _ _ (by omega)), T_gX]
  simp only [gX, gS]
  split_ifs <;> ring

theorem gV_not_mem (a : ℕ → Bool) (r u : ℕ → ℝ) {k : Fin (2 * n)} (hk : k ∉ basisA n a) :
    gV n a r u k = u (k.val / 2) := by
  rw [mem_basisA] at hk
  simp only [gV, gX, gS]
  cases h : a (k.val / 2) <;> simp only [h, Bool.false_eq_true, iff_false, iff_true,
    not_not] at hk <;> simp [hk]

/-! ### `basisA n a` is a feasible, nondegenerate basis -/

theorem X_nonneg {x : Fin (2 * n) → ℝ} (hx : ∀ k, 0 ≤ x k) (j : ℕ) : 0 ≤ X x j := by
  simp only [X, ext]; split_ifs
  · exact hx _
  · exact le_refl _

theorem S_nonneg {x : Fin (2 * n) → ℝ} (hx : ∀ k, 0 ≤ x k) (j : ℕ) : 0 ≤ S x j := by
  simp only [S, ext]; split_ifs
  · exact hx _
  · exact le_refl _

theorem isBasis_basisA (a : ℕ → Bool) : (P n).IsBasis (basisA n a) := by
  refine ⟨card_basisA a, (LP.linIndep_iff _ _).2 fun x hx hAx ↦ ?_⟩
  have hrow : ∀ i (hi : i < n), X x i + S x i + 2 * T (X x) i = 0 := by
    intro i hi
    have := congrFun hAx ⟨i, hi⟩
    rwa [mulVec_apply] at this
  have hnb : ∀ i (hi : i < n), (a i = true → S x i = 0) ∧ (a i = false → X x i = 0) := by
    intro i hi
    constructor
    · intro ha
      have hk : (⟨2 * i + 1, by omega⟩ : Fin (2 * n)) ∉ basisA n a := by
        rw [mem_basisA_s, ha]; simp
      have := hx _ hk
      simp only [S, ext, show 2 * i + 1 < 2 * n by omega, dite_true]
      exact this
    · intro ha
      have hk : (⟨2 * i, by omega⟩ : Fin (2 * n)) ∉ basisA n a := by
        rw [mem_basisA_x, ha]; simp
      have := hx _ hk
      simp only [X, ext, show 2 * i < 2 * n by omega, dite_true]
      exact this
  have hz : ∀ i, i < n → X x i = 0 ∧ S x i = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have hT : T (X x) i = 0 := by
        refine sum_eq_zero fun j hj ↦ ?_
        rw [(ih j (mem_range.1 hj) (by have := mem_range.1 hj; omega)).1, mul_zero]
      have h := hrow i hi
      rw [hT] at h
      cases ha : a i
      · have h0 := (hnb i hi).2 ha
        exact ⟨h0, by linarith⟩
      · have h0 := (hnb i hi).1 ha
        exact ⟨by linarith, h0⟩
  funext k
  have hk := k.isLt
  rw [apply_eq x k]
  split_ifs
  · exact (hz _ (by omega)).1
  · exact (hz _ (by omega)).2

/-- The right-hand side `b`, as a function on `ℕ`. -/
def bvec (i : ℕ) : ℝ := 100 ^ i

theorem basicSol_basisA (a : ℕ → Bool) :
    (P n).basicSol (basisA n a) = gV n a bvec (fun _ ↦ 0) := by
  refine ((isBasis_basisA a).eq_basicSol ?_ fun k hk ↦ ?_).symm
  · rw [mulVec_gV]; funext i; rw [b_apply]; rfl
  · rw [gV_not_mem _ _ _ hk]

/-- Bounds for `T` along the basic solution: `0 ≤ T_i ≤ 100^i / 10`. -/
theorem gT_basic_bound (a : ℕ → Bool) (i : ℕ) :
    0 ≤ gT a bvec (fun _ ↦ 0) i ∧ 10 * gT a bvec (fun _ ↦ 0) i ≤ 100 ^ i := by
  induction i with
  | zero => simp [gT_zero]
  | succ i ih =>
    rw [gT_succ, gX, pow_succ]
    have hp : (0 : ℝ) ≤ 100 ^ i := by positivity
    simp only [bvec]
    split_ifs <;> constructor <;> nlinarith

theorem gX_basic_pos (a : ℕ → Bool) (i : ℕ) :
    0 < (100 : ℝ) ^ i - 0 - 2 * gT a bvec (fun _ ↦ 0) i := by
  have := gT_basic_bound a i
  have hp : (0 : ℝ) < 100 ^ i := by positivity
  linarith

theorem basicSol_basisA_apply (a : ℕ → Bool) (k : Fin (2 * n)) :
    (P n).basicSol (basisA n a) k =
      if k ∈ basisA n a then 100 ^ (k.val / 2) - 2 * gT a bvec (fun _ ↦ 0) (k.val / 2)
      else 0 := by
  rw [basicSol_basisA]
  split_ifs with hk
  · rw [mem_basisA] at hk
    simp only [gV, gX, gS, bvec]
    cases h : a (k.val / 2) <;> simp only [h, Bool.false_eq_true, iff_false, iff_true,
      ↓reduceIte] at hk ⊢ <;> simp [hk]
  · rw [gV_not_mem _ _ _ hk]

theorem basicSol_basisA_pos (a : ℕ → Bool) {k : Fin (2 * n)} (hk : k ∈ basisA n a) :
    0 < (P n).basicSol (basisA n a) k := by
  rw [basicSol_basisA_apply, ite_eq_left hk]
  simpa using gX_basic_pos a (k.val / 2)

theorem isFeasibleBasis_basisA (a : ℕ → Bool) : (P n).IsFeasibleBasis (basisA n a) := by
  refine ⟨isBasis_basisA a, fun k ↦ ?_⟩
  by_cases hk : k ∈ basisA n a
  · exact le_of_lt (basicSol_basisA_pos a hk)
  · rw [basicSol_basisA_apply, ite_eq_right hk]

theorem isNondegenerate_basisA (a : ℕ → Bool) : (P n).IsNondegenerate (basisA n a) :=
  fun _ hk ↦ basicSol_basisA_pos a hk

/-! ### Feasible points and feasible bases -/

/-- On feasible points: `x_i + s_i > 0` and `x_i, s_i ≤ 100^i`. -/
theorem feasible_bound {x : Fin (2 * n) → ℝ} (hx : (P n).IsFeasible x) (i : ℕ) (hi : i < n) :
    0 < X x i + S x i ∧ X x i ≤ 100 ^ i ∧ S x i ≤ 100 ^ i := by
  have hrow : ∀ i (hi : i < n), X x i + S x i + 2 * T (X x) i = 100 ^ i := by
    intro i hi
    have := congrFun hx.1 ⟨i, hi⟩
    rwa [mulVec_apply, b_apply] at this
  have inv : ∀ i ≤ n, 0 ≤ T (X x) i ∧ 10 * T (X x) i ≤ 100 ^ i := by
    intro i
    induction i with
    | zero => simp [T_zero]
    | succ i ih =>
      intro hi
      obtain ⟨h1, h2⟩ := ih (by omega)
      have h3 := hrow i (by omega)
      have h4 := X_nonneg hx.2 i
      have h5 := S_nonneg hx.2 i
      rw [T_succ, pow_succ]
      constructor <;> nlinarith
  obtain ⟨h1, h2⟩ := inv i (by omega)
  have h3 := hrow i hi
  have h4 := X_nonneg hx.2 i
  have h5 := S_nonneg hx.2 i
  have hp : (0 : ℝ) < 100 ^ i := by positivity
  refine ⟨by linarith, by linarith, by linarith⟩

theorem feasible_le {x : Fin (2 * n) → ℝ} (hx : (P n).IsFeasible x) (k : Fin (2 * n)) :
    x k ≤ 100 ^ n := by
  have hk := k.isLt
  have hle : (100 : ℝ) ^ (k.val / 2) ≤ 100 ^ n :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hb := feasible_bound hx (k.val / 2) (by omega)
  rw [apply_eq x k]
  split_ifs <;> linarith [hb.2.1, hb.2.2]

/-- The vector `a` read off from a label set `B`: `a j = true` iff `x_j ∈ B`. -/
def aOf (B : Finset (Fin (2 * n))) (j : ℕ) : Bool :=
  if h : 2 * j < 2 * n then decide ((⟨2 * j, h⟩ : Fin (2 * n)) ∈ B) else false

theorem aOf_basisA (a : ℕ → Bool) {j : ℕ} (hj : j < n) : aOf (basisA n a) j = a j := by
  have h1 : 2 * j < 2 * n := by omega
  simp only [aOf, h1, dite_true]
  have := mem_basisA_x (a := a) h1
  cases h : a j <;> simp_all

/-- Every feasible basis is one of the bases `basisA n a`. -/
theorem feasibleBasis_eq {B : Finset (Fin (2 * n))} (hB : (P n).IsFeasibleBasis B) :
    B = basisA n (aOf B) := by
  have hfeas : (P n).IsFeasible ((P n).basicSol B) := ⟨hB.1.basicSol_spec.1, hB.2⟩
  have hpair : ∀ i (hi : i < n), (⟨2 * i, by omega⟩ : Fin (2 * n)) ∈ B ∨
      (⟨2 * i + 1, by omega⟩ : Fin (2 * n)) ∈ B := by
    intro i hi
    by_contra hne
    push Not at hne
    have h := (feasible_bound hfeas i hi).1
    have h1 := hB.1.basicSol_spec.2 _ hne.1
    have h2 := hB.1.basicSol_spec.2 _ hne.2
    simp only [X, S, ext, show 2 * i < 2 * n by omega, show 2 * i + 1 < 2 * n by omega,
      dite_true, h1, h2] at h
    linarith
  symm
  refine eq_of_subset_of_card_le (fun k hk ↦ ?_) (by rw [card_basisA, hB.1.1])
  have hk2 := k.isLt
  rw [mem_basisA] at hk
  have hk1 : 2 * (k.val / 2) < 2 * n := by omega
  simp only [aOf, hk1, dite_true, decide_eq_true_eq] at hk
  by_cases hpar : k.val % 2 = 0
  · have := hk.1 hpar
    convert this using 1
    exact Fin.ext (by simp; omega)
  · have hnot : (⟨2 * (k.val / 2), hk1⟩ : Fin (2 * n)) ∉ B := fun h ↦ hpar (hk.2 h)
    have := (hpair (k.val / 2) (by omega)).resolve_left hnot
    convert this using 1
    exact Fin.ext (by simp; omega)

/-! ### Basic directions and reduced costs -/

/-- `sg a k i = ∏_{k ≤ l < i} (-1)^{a l}`. -/
def sg (a : ℕ → Bool) (k i : ℕ) : ℝ := ∏ l ∈ Ico k i, (if a l then (-1 : ℝ) else 1)

theorem sg_cases (a : ℕ → Bool) (k i : ℕ) : sg a k i = 1 ∨ sg a k i = -1 := by
  unfold sg
  refine prod_induction _ (fun x ↦ x = 1 ∨ x = -1) ?_ (Or.inl rfl) ?_
  · rintro x y (rfl | rfl) (rfl | rfl) <;> norm_num
  · intro l _
    split_ifs <;> simp

theorem sg_congr {a a' : ℕ → Bool} (h : ∀ j < n, a j = a' j) (k : ℕ) :
    sg a k n = sg a' k n := by
  refine prod_congr rfl fun l hl ↦ ?_
  rw [h l (mem_Ico.1 hl).2]

theorem sg_succ (a : ℕ → Bool) {k i : ℕ} (h : k ≤ i) :
    sg a k (i + 1) = sg a k i * (if a i then -1 else 1) := by
  rw [sg, prod_Ico_succ_top h, ← sg]

/-- The unit vector `δ_k` on `ℕ`. -/
def delta (k : ℕ) (i : ℕ) : ℝ := if i = k then 1 else 0

theorem basicDir_basisA (a : ℕ → Bool) (k : Fin n) :
    (P n).basicDir (basisA n a) (wlab a k) = gV n a (fun _ ↦ 0) (delta k) := by
  have hB := isBasis_basisA (n := n) a
  obtain ⟨h1, h2, h3⟩ := hB.basicDir_spec (wlab_not_mem a k)
  have h := hB.eq_zero (x := (P n).basicDir (basisA n a) (wlab a k) -
      gV n a (fun _ ↦ 0) (delta k)) ?_ ?_
  · exact sub_eq_zero.1 h
  · intro j hj
    rw [Pi.sub_apply, gV_not_mem _ _ _ hj]
    by_cases hjk : j = wlab a k
    · subst hjk
      rw [h2, wlab_div, delta, ite_eq_left rfl, sub_self]
    · rw [h3 j hj hjk, delta, ite_eq_right, sub_self]
      intro hjk'
      apply hjk
      rw [not_mem_basisA hj]
      congr 1
      exact Fin.ext hjk'
  · rw [mulVec_sub, h1, mulVec_gV, sub_eq_zero]
    rfl

theorem gT_dir_le (a : ℕ → Bool) (k : ℕ) : ∀ i ≤ k, gT a (fun _ ↦ 0) (delta k) i = 0 := by
  intro i
  induction i with
  | zero => intro; rfl
  | succ i ih =>
    intro hi
    have hik : i ≠ k := by omega
    rw [gT_succ, gX, ih (by omega), delta, ite_eq_right hik]
    split_ifs <;> ring

theorem gT_dir (a : ℕ → Bool) (k : ℕ) : ∀ i, k ≤ i →
    gT a (fun _ ↦ 0) (delta k) (i + 1) = sg a k (i + 1) * 10 ^ (i + 1 - k) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    rw [gT_succ, gX, gT_dir_le a k k le_rfl, delta, ite_eq_left rfl, sg,
      Nat.Ico_succ_singleton, prod_singleton, show k + 1 - k = 1 by omega]
    split_ifs <;> ring
  | succ i hki ih =>
    have hik : i + 1 ≠ k := by omega
    rw [gT_succ, gX, ih, delta, ite_eq_right hik, sg_succ a (show k ≤ i + 1 by omega),
      show i + 1 + 1 - k = (i + 1 - k) + 1 by omega, pow_succ]
    split_ifs <;> ring

/-- The reduced cost of the nonbasic label of pair `k`: `-sg a k n · 10^{n-k} / 10`. -/
theorem reducedCost_wlab (a : ℕ → Bool) (k : Fin n) :
    (P n).reducedCost (basisA n a) (wlab a k) = -(sg a k n * 10 ^ (n - k)) / 10 := by
  have hB := isBasis_basisA (n := n) a
  rw [← hB.cost_basicDir (wlab_not_mem a k), basicDir_basisA, cost_apply]
  have h := T_eq_cost (X (gV n a (fun _ ↦ 0) (delta k))) n
  rw [T_congr (Y' := gX a (fun _ ↦ 0) (delta k)) (fun j hj ↦ X_gV _ _ _ hj), T_gX] at h
  have hk := k.isLt
  have h2 : gT a (fun _ ↦ 0) (delta k) n = sg a k n * 10 ^ (n - k) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact gT_dir a k m (by omega)
  rw [h2] at h
  linarith

theorem mem_improving (a : ℕ → Bool) (j : Fin (2 * n)) :
    j ∈ (P n).improving (basisA n a) ↔ ∃ k : Fin n, j = wlab a k ∧ sg a k n = 1 := by
  have hB := isBasis_basisA (n := n) a
  simp only [LP.improving, mem_filter, mem_univ, true_and]
  constructor
  · intro hj
    have hjB : j ∉ basisA n a := fun h ↦ by
      rw [hB.reducedCost_of_mem h] at hj; exact lt_irrefl _ hj
    refine ⟨_, not_mem_basisA hjB, ?_⟩
    rw [not_mem_basisA hjB, reducedCost_wlab] at hj
    rcases sg_cases a (j.val / 2) n with h | h
    · exact h
    · rw [h] at hj
      have : (0 : ℝ) < 10 ^ (n - j.val / 2) := by positivity
      linarith
  · rintro ⟨k, rfl, hk⟩
    rw [reducedCost_wlab, hk]
    have : (0 : ℝ) < 10 ^ (n - k.val) := by positivity
    linarith

/-! ### Pivots -/

/-- `a` with the entry `k` flipped. -/
def flipAt (a : ℕ → Bool) (k : ℕ) : ℕ → Bool := fun j ↦ if j = k then !a j else a j

/-- The pivot on the nonbasic label of pair `k` swaps the two labels of pair `k`
(the leaving label is the basic label of pair `k`). -/
theorem pivot_eq (a : ℕ → Bool) (k : Fin n) {i : Fin (2 * n)}
    (himp : wlab a k ∈ (P n).improving (basisA n a))
    (hi : (P n).IsLeavingLabel (basisA n a) (wlab a k) i) :
    insert (wlab a k) ((basisA n a).erase i) = basisA n (flipAt a k) := by
  have hf := (LP.pivot_spec (isFeasibleBasis_basisA a) himp hi).1
  have hB' := feasibleBasis_eq hf
  have hiv : i = vlab a k := by
    by_contra hne
    apply not_both a (aOf (insert (wlab a k) ((basisA n a).erase i))) k
    rw [← hB']
    exact ⟨mem_insert_of_mem (mem_erase.2 ⟨Ne.symm hne, vlab_mem a k⟩), mem_insert_self _ _⟩
  subst hiv
  ext j
  have hj := j.isLt
  have hk := k.isLt
  simp only [mem_insert, mem_erase, mem_basisA, Fin.ext_iff, vlab_val, wlab_val, flipAt, ne_eq]
  by_cases hjk : j.val / 2 = k.val
  · simp only [hjk, ↓reduceIte]
    cases h : a k.val <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, iff_true, iff_false] <;> omega
  · simp only [hjk, ↓reduceIte]
    generalize a (j.val / 2) = b
    have h1 : ¬ j.val = 2 * k.val + (if a k.val then 1 else 0) := by split_ifs <;> omega
    have h2 : ¬ j.val = 2 * k.val + (if a k.val then 0 else 1) := by split_ifs <;> omega
    simp only [h1, h2, false_or, not_false_eq_true, true_and]

/-! ### Dantzig's rule and Bland's rule choose the least improving pair -/

/-- Pair `k` is improving, and no pair with a smaller index is improving. -/
def LeastImp (a : ℕ → Bool) (k : Fin n) : Prop :=
  sg a k n = 1 ∧ ∀ l < k.val, sg a l n ≠ 1

theorem dantzig_iff (a : ℕ → Bool) (j : Fin (2 * n)) :
    (P n).IsDantzigChoice (basisA n a) j ↔ ∃ k : Fin n, j = wlab a k ∧ LeastImp a k := by
  constructor
  · rintro ⟨hj, hmin⟩
    obtain ⟨k, rfl, hk⟩ := (mem_improving a j).1 hj
    refine ⟨k, rfl, hk, fun l hl hsl ↦ ?_⟩
    have hln : l < n := by have := k.isLt; omega
    have h := hmin (wlab a ⟨l, hln⟩) ((mem_improving a _).2 ⟨_, rfl, hsl⟩)
    rw [reducedCost_wlab, reducedCost_wlab, hk] at h
    simp only at h
    rw [hsl] at h
    have : (10 : ℝ) ^ (n - k.val) < 10 ^ (n - l) :=
      pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith
  · rintro ⟨k, rfl, hk, hmin⟩
    refine ⟨(mem_improving a _).2 ⟨k, rfl, hk⟩, fun i hi ↦ ?_⟩
    obtain ⟨l, rfl, hl⟩ := (mem_improving a i).1 hi
    have hkl : k.val ≤ l.val := by
      by_contra h
      exact hmin l (by omega) hl
    rw [reducedCost_wlab, reducedCost_wlab, hk, hl]
    have : (10 : ℝ) ^ (n - l.val) ≤ 10 ^ (n - k.val) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith

theorem bland_iff (a : ℕ → Bool) (j : Fin (2 * n)) :
    (P n).IsBlandChoice Fin.val (basisA n a) j ↔ ∃ k : Fin n, j = wlab a k ∧ LeastImp a k := by
  constructor
  · rintro ⟨hj, hmin⟩
    obtain ⟨k, rfl, hk⟩ := (mem_improving a j).1 hj
    refine ⟨k, rfl, hk, fun l hl hsl ↦ ?_⟩
    have hln : l < n := by have := k.isLt; omega
    have h := hmin (wlab a ⟨l, hln⟩) ((mem_improving a _).2 ⟨_, rfl, hsl⟩)
    rw [wlab_val, wlab_val] at h
    simp only at h
    split_ifs at h <;> omega
  · rintro ⟨k, rfl, hk, hmin⟩
    refine ⟨(mem_improving a _).2 ⟨k, rfl, hk⟩, fun i hi ↦ ?_⟩
    obtain ⟨l, rfl, hl⟩ := (mem_improving a i).1 hi
    have hkl : k.val ≤ l.val := by
      by_contra h
      exact hmin l (by omega) hl
    rcases eq_or_lt_of_le hkl with h | h
    · rw [Fin.ext h]
    · rw [wlab_val, wlab_val]
      split_ifs <;> omega

/-! ### The counter -/

/-- The counter `v(a) = ∑_{k<n, sg a k n ≠ 1} 2^k`. -/
noncomputable def v (n : ℕ) (a : ℕ → Bool) : ℕ :=
  ∑ k ∈ range n, if sg a k n = 1 then 0 else 2 ^ k

theorem geom_two (k : ℕ) : ∑ j ∈ range k, 2 ^ j + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, pow_succ]; omega

theorem v_congr {a a' : ℕ → Bool} (h : ∀ j < n, a j = a' j) : v n a = v n a' := by
  refine sum_congr rfl fun k _ ↦ ?_
  rw [sg_congr h]

theorem v_zero : v n (fun _ ↦ false) = 0 := by
  refine sum_eq_zero fun k _ ↦ ?_
  simp [sg]

theorem v_le (a : ℕ → Bool) : v n a ≤ 2 ^ n - 1 := by
  have h1 : v n a ≤ ∑ j ∈ range n, 2 ^ j :=
    sum_le_sum fun k _ ↦ by split_ifs <;> simp
  have := geom_two n
  omega

theorem v_top (a : ℕ → Bool) : v n a = 2 ^ n - 1 ↔ ∀ k < n, sg a k n ≠ 1 := by
  have hg := geom_two n
  constructor
  · intro hv k hk hs
    have hkr : k ∈ range n := mem_range.2 hk
    have h1 : v n a = ∑ j ∈ (range n).erase k, if sg a j n = 1 then 0 else 2 ^ j := by
      rw [v, ← add_sum_erase _ _ hkr, hs, ite_eq_left rfl, zero_add]
    have h2 : ∑ j ∈ (range n).erase k, (if sg a j n = 1 then 0 else 2 ^ j) ≤
        ∑ j ∈ (range n).erase k, 2 ^ j :=
      sum_le_sum fun k _ ↦ by split_ifs <;> simp
    have h3 := add_sum_erase _ (fun j ↦ 2 ^ j) hkr
    have h4 : 0 < 2 ^ k := by positivity
    omega
  · intro h
    have : v n a = ∑ j ∈ range n, 2 ^ j :=
      sum_congr rfl fun k hk ↦ by rw [ite_eq_right (h k (mem_range.1 hk))]
    omega

theorem sg_flipAt_le (a : ℕ → Bool) {k l : ℕ} (hlk : l ≤ k) (hk : k < n) :
    sg (flipAt a k) l n = -sg a l n := by
  have hkI : k ∈ Ico l n := mem_Ico.2 ⟨hlk, hk⟩
  unfold sg
  rw [← mul_prod_erase _ _ hkI, ← mul_prod_erase _ (fun l ↦ if a l then (-1 : ℝ) else 1) hkI,
    prod_congr rfl (g := fun l ↦ if a l then (-1 : ℝ) else 1)]
  · simp only [flipAt, ↓reduceIte]
    cases a k <;> norm_num
  · intro j hj
    simp only [flipAt, ne_of_mem_erase hj, ↓reduceIte]

theorem sg_flipAt_gt (a : ℕ → Bool) {k l : ℕ} (hkl : k < l) :
    sg (flipAt a k) l n = sg a l n := by
  refine prod_congr rfl fun j hj ↦ ?_
  have : j ≠ k := by have := (mem_Ico.1 hj).1; omega
  simp only [flipAt, this, ↓reduceIte]

theorem sg_ne_one {a : ℕ → Bool} {k i : ℕ} (h : sg a k i ≠ 1) : sg a k i = -1 :=
  (sg_cases a k i).resolve_left h

theorem v_flipAt (a : ℕ → Bool) (k : Fin n) (hk : LeastImp a k) :
    v n (flipAt a k) = v n a + 1 := by
  have hkn := k.isLt
  have e1 : ∑ j ∈ range k.val, (if sg (flipAt a k) j n = 1 then 0 else 2 ^ j) = 0 :=
    sum_eq_zero fun j hj ↦ by
      have hjk := mem_range.1 hj
      rw [sg_flipAt_le a hjk.le hkn, sg_ne_one (hk.2 j hjk), ite_eq_left (by norm_num)]
  have e2 : ∑ j ∈ range k.val, (if sg a j n = 1 then 0 else 2 ^ j) =
      ∑ j ∈ range k.val, 2 ^ j :=
    sum_congr rfl fun j hj ↦ ite_eq_right (hk.2 j (mem_range.1 hj))
  have e3 : ∑ j ∈ Ico (k.val + 1) n, (if sg (flipAt a k) j n = 1 then 0 else 2 ^ j) =
      ∑ j ∈ Ico (k.val + 1) n, (if sg a j n = 1 then 0 else 2 ^ j) :=
    sum_congr rfl fun j hj ↦ by
      rw [sg_flipAt_gt a (show k.val < j by have := (mem_Ico.1 hj).1; omega)]
  have e4 : (if sg (flipAt a k) k.val n = 1 then 0 else 2 ^ k.val) = 2 ^ k.val := by
    rw [sg_flipAt_le a le_rfl hkn, hk.1, ite_eq_right (by norm_num)]
  have e5 : (if sg a k.val n = 1 then 0 else 2 ^ k.val) = 0 := by rw [hk.1, ite_eq_left rfl]
  have h : k.val + 1 ≤ n := by omega
  unfold v
  rw [← sum_range_add_sum_Ico _ h, ← sum_range_add_sum_Ico _ h, sum_range_succ,
    sum_range_succ, e1, e2, e3, e4, e5]
  have := geom_two k.val
  omega

/-! ### Admissibility -/

/-- The all-slack vector: `a i = false` for all `i`. -/
def a0 : ℕ → Bool := fun _ ↦ false

theorem slack_eq (n : ℕ) : basisOf (kmSlack n) = basisA n a0 := by
  unfold basisOf basisA
  congr 1

theorem bounded (n : ℕ) : (P n).FeasibleSetNonemptyBounded := by
  refine ⟨⟨_, (isFeasibleBasis_basisA (n := n) a0).1.basicSol_spec.1,
    (isFeasibleBasis_basisA a0).2⟩, 100 ^ n, fun x hx j ↦ ?_⟩
  rw [abs_of_nonneg (hx.2 j)]
  exact feasible_le hx j

theorem rank_eq (n : ℕ) : (P n).A.rank = n := by
  have hsurj : Function.Surjective (P n).A.mulVecLin := by
    intro r
    refine ⟨gV n a0 (fun i ↦ if h : i < n then r ⟨i, h⟩ else 0) (fun _ ↦ 0), ?_⟩
    rw [Matrix.mulVecLin_apply, mulVec_gV]
    funext i
    simp [i.isLt]
  rw [Matrix.rank, LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fin_fun]

/-! ### Runs -/

section Runs

variable (C : Finset (Fin (2 * n)) → Fin (2 * n) → Prop)

/-- One step of a run with a rule that chooses the least improving pair increases the
counter by one. -/
theorem step_v (hC : ∀ a j, C (basisA n a) j ↔ ∃ k : Fin n, j = wlab a k ∧ LeastImp a k)
    {B B' : Finset (Fin (2 * n))} {j : Fin (2 * n)} (hB : (P n).IsFeasibleBasis B)
    (hc : C B j) (hp : (P n).IsPivot B j B') : v n (aOf B') = v n (aOf B) + 1 := by
  have hBa := feasibleBasis_eq hB
  rw [hBa] at hc hp
  obtain ⟨k, rfl, hk⟩ := (hC _ j).1 hc
  obtain ⟨_, himp, _, i, hi, hB'⟩ := hp
  rw [hB', pivot_eq _ k himp hi, v_congr (fun j hj ↦ aOf_basisA _ hj), v_flipAt _ k hk]

theorem partial_v (hC : ∀ a j, C (basisA n a) j ↔ ∃ k : Fin n, j = wlab a k ∧ LeastImp a k)
    {f : ℕ} {B : ℕ → Finset (Fin (2 * n))} (hrun : (P n).IsPartialSimplexRunWith C f B)
    (h0 : B 0 = basisA n a0) : ∀ k ≤ f, v n (aOf (B k)) = k := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [h0, v_congr (fun j hj ↦ aOf_basisA _ hj)]
    exact v_zero
  | succ k ih =>
    intro hk
    obtain ⟨j, hc, hp⟩ := hrun.2 k (by omega)
    rw [step_v C hC (hrun.1 k (by omega)) hc hp, ih (by omega)]

theorem partial_le (hC : ∀ a j, C (basisA n a) j ↔ ∃ k : Fin n, j = wlab a k ∧ LeastImp a k)
    {f : ℕ} {B : ℕ → Finset (Fin (2 * n))} (hrun : (P n).IsPartialSimplexRunWith C f B)
    (h0 : B 0 = basisA n a0) : f ≤ 2 ^ n - 1 := by
  rw [← partial_v C hC hrun h0 f le_rfl]
  exact v_le _

theorem run_eq (hC : ∀ a j, C (basisA n a) j ↔ ∃ k : Fin n, j = wlab a k ∧ LeastImp a k)
    {f : ℕ} {B : ℕ → Finset (Fin (2 * n))} (hrun : (P n).IsSimplexRunWith C f B)
    (h0 : B 0 = basisA n a0) : f = 2 ^ n - 1 := by
  rw [← partial_v C hC hrun.1 h0 f le_rfl]
  have hBf := feasibleBasis_eq (hrun.1.1 f le_rfl)
  have hemp := hrun.2
  rw [hBf] at hemp
  refine (v_top _).2 fun k hk hs ↦ ?_
  have := (mem_improving _ (wlab (aOf (B f)) ⟨k, hk⟩)).2 ⟨_, rfl, hs⟩
  rw [hemp] at this
  exact notMem_empty _ this

/-- The next vector: flip the least improving pair (if there is one). -/
noncomputable def nxt (a : ℕ → Bool) : ℕ → Bool :=
  if h : ∃ k, k < n ∧ sg a k n = 1 then flipAt a (Nat.find h) else a

theorem exists_least (a : ℕ → Bool) (h : ∃ k, k < n ∧ sg a k n = 1) :
    ∃ k : Fin n, LeastImp a k ∧ nxt (n := n) a = flipAt a k := by
  refine ⟨⟨Nat.find h, (Nat.find_spec h).1⟩, ⟨(Nat.find_spec h).2, fun l hl hs ↦ ?_⟩, ?_⟩
  · have h1 : Nat.find h < n := (Nat.find_spec h).1
    have h2 : l < Nat.find h := hl
    exact Nat.find_min h h2 ⟨by omega, hs⟩
  · rw [nxt, dite_eq_left h]

theorem seq_v (m : ℕ) (hm : m ≤ 2 ^ n - 1) : v n ((nxt (n := n))^[m] a0) = m := by
  induction m with
  | zero => exact v_zero
  | succ m ih =>
    have ih := ih (by omega)
    have h : ∃ k, k < n ∧ sg ((nxt (n := n))^[m] a0) k n = 1 := by
      by_contra hne
      push Not at hne
      have := (v_top (n := n) _).2 hne
      omega
    obtain ⟨k, hk, hnx⟩ := exists_least _ h
    rw [Function.iterate_succ_apply', hnx, v_flipAt _ k hk, ih]

theorem exists_run (hC : ∀ a j, C (basisA n a) j ↔ ∃ k : Fin n, j = wlab a k ∧ LeastImp a k) :
    ∃ f B, (P n).IsSimplexRunWith C f B ∧ B 0 = basisA n a0 := by
  refine ⟨2 ^ n - 1, fun m ↦ basisA n ((nxt (n := n))^[m] a0),
    ⟨⟨fun m _ ↦ isFeasibleBasis_basisA _, fun m hm ↦ ?_⟩, ?_⟩, rfl⟩
  · set a := (nxt (n := n))^[m] a0
    have hv : v n a = m := seq_v (n := n) m (by omega)
    have h : ∃ k, k < n ∧ sg a k n = 1 := by
      by_contra hne
      push Not at hne
      have := (v_top (n := n) _).2 hne
      omega
    obtain ⟨k, hk, hnx⟩ := exists_least _ h
    have himp := (mem_improving a (wlab a k)).2 ⟨k, rfl, hk.1⟩
    obtain ⟨i, hi⟩ := LP.exists_leavingLabel (bounded n) (isFeasibleBasis_basisA a) himp
    refine ⟨wlab a k, (hC a _).2 ⟨k, rfl, hk⟩,
      isFeasibleBasis_basisA a, himp, wlab_not_mem a k, i, hi, ?_⟩
    simp only
    rw [Function.iterate_succ_apply', hnx, pivot_eq a k himp hi]
  · have hv := (v_top _).1 (seq_v (n := n) (2 ^ n - 1) le_rfl)
    refine eq_empty_of_forall_notMem fun j hj ↦ ?_
    obtain ⟨k, -, hk⟩ := (mem_improving _ j).1 hj
    exact hv k k.isLt hk

end Runs

/-! ### Main statements -/

theorem basicSol_slack (n : ℕ) : (kleeMinty n).toLP.basicSol (basisOf (kmSlack n)) =
    fun k ↦ if k.val % 2 = 1 then (100 : ℝ) ^ (k.val / 2) else 0 := by
  have hT : ∀ i, gT a0 bvec (fun _ ↦ 0) i = 0 := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [gT_succ, gX, ih, show a0 i = false from rfl]; simp
  rw [slack_eq, basicSol_basisA]
  funext k
  simp only [gV, gX, gS, hT, a0, bvec]
  split_ifs <;> first | contradiction | rfl | omega | simp

theorem admissible (n : ℕ) (hn : 1 ≤ n) :
    (kleeMinty n).IsAdmissible ∧ (kleeMinty n).toLP.IsFeasibleBasis (basisOf (kmSlack n)) := by
  refine ⟨⟨hn, rank_eq n, bounded n, fun B hB ↦ ?_⟩, ?_⟩
  · rw [feasibleBasis_eq hB]
    exact isNondegenerate_basisA _
  · rw [slack_eq]
    exact isFeasibleBasis_basisA _

-- `hn` is not needed for the proof (the statements also hold for `n = 0`); it is kept
-- in the given statement.
set_option linter.unusedVariables false in
theorem dantzig (n : ℕ) (hn : 1 ≤ n) :
    (∃ f B, (kleeMinty n).toLP.IsSimplexRunWith (kleeMinty n).toLP.IsDantzigChoice f B ∧
      B 0 = basisOf (kmSlack n)) ∧
    (∀ f B, (kleeMinty n).toLP.IsSimplexRunWith (kleeMinty n).toLP.IsDantzigChoice f B →
      B 0 = basisOf (kmSlack n) → f = 2 ^ n - 1) ∧
    (∀ f B, (kleeMinty n).toLP.IsPartialSimplexRunWith (kleeMinty n).toLP.IsDantzigChoice f B →
      B 0 = basisOf (kmSlack n) → f ≤ 2 ^ n - 1) ∧
    (∀ B, (kleeMinty n).toLP.IsFeasibleBasis B → ∀ j j',
      (kleeMinty n).toLP.IsDantzigChoice B j → (kleeMinty n).toLP.IsDantzigChoice B j' →
        j = j') := by
  rw [slack_eq]
  refine ⟨exists_run _ dantzig_iff, fun f B h h0 ↦ run_eq _ dantzig_iff h h0,
    fun f B h h0 ↦ partial_le _ dantzig_iff h h0, fun B hB j j' hj hj' ↦ ?_⟩
  rw [feasibleBasis_eq hB] at hj hj'
  obtain ⟨k, rfl, hk⟩ := (dantzig_iff _ _).1 hj
  obtain ⟨k', rfl, hk'⟩ := (dantzig_iff _ _).1 hj'
  have : k = k' := by
    rcases lt_trichotomy k.val k'.val with h | h | h
    · exact absurd hk.1 (hk'.2 _ h)
    · exact Fin.ext h
    · exact absurd hk'.1 (hk.2 _ h)
  rw [this]

-- `hn` is not needed for the proof (the statements also hold for `n = 0`); it is kept
-- in the given statement.
set_option linter.unusedVariables false in
theorem bland (n : ℕ) (hn : 1 ≤ n) :
    (∃ f B, (kleeMinty n).toLP.IsSimplexRunWith ((kleeMinty n).toLP.IsBlandChoice Fin.val) f B ∧
      B 0 = basisOf (kmSlack n)) ∧
    (∀ f B, (kleeMinty n).toLP.IsSimplexRunWith ((kleeMinty n).toLP.IsBlandChoice Fin.val) f B →
      B 0 = basisOf (kmSlack n) → f = 2 ^ n - 1) ∧
    (∀ f B, (kleeMinty n).toLP.IsPartialSimplexRunWith
        ((kleeMinty n).toLP.IsBlandChoice Fin.val) f B →
      B 0 = basisOf (kmSlack n) → f ≤ 2 ^ n - 1) := by
  rw [slack_eq]
  exact ⟨exists_run _ bland_iff, fun f B h h0 ↦ run_eq _ bland_iff h h0,
    fun f B h h0 ↦ partial_le _ bland_iff h h0⟩

end KM

end WolfeSimplex
