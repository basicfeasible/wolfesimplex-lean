import WolfeSimplex.Execution.Preparation
import WolfeSimplex.Execution.Machine

/-! Bounds for the literal array addresses in the generated code, separately
from the numeric data tracked by `run.peak`. Control counters are bounded by work. -/
namespace WolfeSimplex.Execution
open Code
variable {m n : ℕ}

namespace Code
private theorem fold_max_le (xs : List ℕ) (R : ℕ) (h : ∀ i ∈ xs, i ≤ R) :
    xs.foldr Max.max 0 ≤ R := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons i xs ih => exact max_le (h i (by simp)) (ih (fun i hi ↦ h i (by simp [hi])))

theorem address_read (is : List ℕ) (R : ℕ) (h : ∀ i ∈ is, i ≤ R) :
    (read is).addressBound ≤ R := fold_max_le is R h

theorem address_range (r : ℕ) : (read (List.range r)).addressBound ≤ r :=
  address_read _ _ (fun _ hi ↦ (List.mem_range.mp hi).le)

theorem address_slot (block i R : ℕ) (hb : block ≤ R) (hi : i ≤ R) :
    (slot block i).addressBound ≤ R := by simpa [slot, addressBound] using max_le hb hi

theorem address_table (cs : List Code) (R : ℕ) (h : ∀ c ∈ cs, c.addressBound ≤ R) :
    (table cs).addressBound ≤ R := by
  induction cs with
  | nil => exact Nat.zero_le _
  | cons c cs ih => exact max_le (h c (by simp)) (ih (fun c hc ↦ h c (by simp [hc])))

theorem address_add {a b : Code} {R : ℕ} (hR : 1 ≤ R)
    (ha : a.addressBound ≤ R) (hb : b.addressBound ≤ R) : (add a b).addressBound ≤ R := by
  simpa [add, addressBound, and_assoc] using And.intro (And.intro ha hb) hR

theorem address_sub {a b : Code} {R : ℕ} (hR : 1 ≤ R)
    (ha : a.addressBound ≤ R) (hb : b.addressBound ≤ R) : (sub a b).addressBound ≤ R := by
  simpa [sub, addressBound, and_assoc] using And.intro (And.intro ha hb) hR

theorem address_mul {a b : Code} {R : ℕ} (hR : 1 ≤ R)
    (ha : a.addressBound ≤ R) (hb : b.addressBound ≤ R) : (mul a b).addressBound ≤ R := by
  simpa [mul, addressBound, and_assoc] using And.intro (And.intro ha hb) hR

theorem address_max {a b : Code} {R : ℕ} (hR : 1 ≤ R)
    (ha : a.addressBound ≤ R) (hb : b.addressBound ≤ R) : (Code.max a b).addressBound ≤ R := by
  simpa [Code.max, addressBound, and_assoc] using And.intro (And.intro ha hb) hR

theorem address_neg {a : Code} {R : ℕ} (ha : a.addressBound ≤ R) :
    (neg a).addressBound ≤ R := by simpa [neg, addressBound] using ha

theorem address_abs {a : Code} {R : ℕ} (ha : a.addressBound ≤ R) :
    (abs a).addressBound ≤ R := by simpa [abs, addressBound] using ha

theorem address_sign {a : Code} {R : ℕ} (ha : a.addressBound ≤ R) :
    (sign a).addressBound ≤ R := by simpa [sign, addressBound] using ha

theorem address_sum (cs : List Code) (R : ℕ) (hR : 1 ≤ R)
    (h : ∀ c ∈ cs, c.addressBound ≤ R) : (Code.sum cs).addressBound ≤ R := by
  induction cs with
  | nil => exact Nat.zero_le _
  | cons c cs ih =>
    exact address_add hR (h c (by simp)) (ih (fun c hc ↦ h c (by simp [hc])))

theorem address_maxList (cs : List Code) (R : ℕ) (hR : 1 ≤ R)
    (h : ∀ c ∈ cs, c.addressBound ≤ R) : (maxList cs).addressBound ≤ R := by
  induction cs with
  | nil => exact Nat.zero_le _
  | cons c cs ih =>
    exact address_max hR (h c (by simp)) (ih (fun c hc ↦ h c (by simp [hc])))

theorem address_iterate (c : Code) (k R : ℕ) (hc : c.addressBound ≤ R) (ho : c.outputs ≤ R) :
    (iterateCode c k).addressBound ≤ R := by
  induction k with
  | zero => exact (address_range _).trans ho
  | succ k ih => exact max_le hc ih

theorem address_power {c : Code} {R : ℕ} (arity k : ℕ) (hR : 2 ≤ R)
    (hc : c.addressBound ≤ R) : (power arity c k).addressBound ≤ R := by
  have hstep : (par (copy 0) (mul (copy 0) (copy 1))).addressBound ≤ R := by
    simp [copy, mul, addressBound]
    omega
  have ho : (par (copy 0) (mul (copy 0) (copy 1))).outputs ≤ R := by
    simpa [outputs, copy, mul] using hR
  have hi := address_iterate _ k R hstep ho
  simpa [power, copy, addressBound] using And.intro hc (And.intro hi (by omega : 1 ≤ R))

theorem address_chain (cs : List Code) (body : Code) (R : ℕ)
    (hc : ∀ c ∈ cs, c.addressBound ≤ R) (hb : body.addressBound ≤ R) :
    (cacheChain cs body).addressBound ≤ R := by
  induction cs with
  | nil => exact hb
  | cons c cs ih => exact max_le (hc c (by simp)) (ih (fun c hc' ↦ hc c (by simp [hc'])))
end Code

/-- A dimension-only bound, including the two labels/rows of preparation. -/
def addressLimit (m n : ℕ) := 4 * (m + n + 20) ^ 2

private theorem addressFacts (m n : ℕ) :
    10 ≤ addressLimit m n ∧ m + n + 2 ≤ addressLimit m n ∧
      2 * (m + 2) ^ 2 + 2 * (n + 2) ^ 2 ≤ addressLimit m n := by
  dsimp [addressLimit]
  constructor
  · ring_nf; omega
  constructor <;> (ring_nf; omega)

private theorem pairAddress (m n i j : ℕ) (hi : i ≤ m + 1) (hj : j ≤ n + 1) :
    n * i + j ≤ addressLimit m n := by
  have hmul := Nat.mul_le_mul_left n hi
  dsimp [addressLimit]
  ring_nf at hmul ⊢
  omega

private theorem absoluteScan_address (block count R : ℕ) (hR : 1 ≤ R)
    (hb : block ≤ R) (hc : count ≤ R) : (absoluteScan block count).addressBound ≤ R := by
  apply address_maxList _ _ hR
  intro c hm
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
  apply address_abs
  exact address_slot block i.val R hb (i.isLt.le.trans hc)

theorem atomCode_address (m n : ℕ) : (atomCode m n).addressBound ≤ addressLimit m n := by
  let R := addressLimit m n
  have hFacts := addressFacts m n
  have h10 : 10 ≤ R := hFacts.1
  have h1 : 1 ≤ R := by omega
  have h2 : 2 ≤ R := by omega
  have hmR : m ≤ R := by have := hFacts.2.1; omega
  have hm1R : m + 1 ≤ R := by have := hFacts.2.1; omega
  have hn1R : n + 1 ≤ R := by have := hFacts.2.1; omega
  have hmn : m * n ≤ R := by dsimp [R, addressLimit]; nlinarith
  have hnm : (n + 1) * m ≤ R := by dsimp [R, addressLimit]; nlinarith
  have hu : (uCode m n).addressBound ≤ R := address_max h1 (by simpa [addressBound] using h1)
    (address_max h1 (absoluteScan_address 0 _ _ h1 (by omega) hmn)
      (absoluteScan_address 1 _ _ h1 (by omega) hmR))
  have hc : (cCode n).addressBound ≤ R := address_add h1 (by simpa [addressBound] using h1)
    (absoluteScan_address 3 n R h1 (by omega) (by omega))
  have ht : (tCode m).addressBound ≤ R := by
    apply address_add h1 _ (by simpa [addressBound] using h1)
    apply address_mul h1
    · exact address_mul h1 (by simpa [addressBound] using h2) (by simpa only [addressBound, Int.natAbs_natCast] using hmR)
    · apply address_power 0 m h2
      exact address_mul h1 (by simpa only [addressBound, Int.natAbs_natCast] using hmR)
        (address_slot 1 0 R (by omega) (by omega))
  have hg : (gammaCode n).addressBound ≤ R := by
    apply address_table
    intro c hc
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    apply address_add h1 (address_slot 1 0 R (by omega) (by omega))
    split_ifs
    · exact address_slot 5 j.val R (by omega) (j.isLt.le.trans hn1R)
    · exact Nat.zero_le _
  have ha : (alphaCode m n).addressBound ≤ R := by
    apply address_table
    intro c hc
    obtain ⟨ji, rfl⟩ := List.mem_ofFn.mp hc
    apply address_sub h1
    · apply address_mul h1 (address_slot 1 0 R (by omega) (by omega))
      split_ifs
      · exact address_slot 4 _ R (by omega)
          (pairAddress m n ji.modNat.val ji.divNat.val (by have := ji.modNat.isLt; omega)
            (by have := ji.divNat.isLt; omega))
      · exact Nat.zero_le _
    · exact address_slot 5 _ R (by omega) (ji.modNat.isLt.le.trans hmR)
  have hk : (kCode m n).addressBound ≤ R := address_max h1 (by simpa [addressBound] using h1)
    (address_max h1 (absoluteScan_address 0 _ _ h1 (by omega) hnm)
      (absoluteScan_address 1 _ _ h1 (by omega) hn1R))
  have hh : (hCode m).addressBound ≤ R := by
    apply address_power 0 (m + 1) h2
    apply address_mul h1 (by simpa only [addressBound, Int.natAbs_natCast] using hm1R)
    exact address_mul h1 (address_slot 0 0 R (by omega) (by omega))
      (address_slot 0 0 R (by omega) (by omega))
  have hn : (nCode m).addressBound ≤ R := by
    apply address_mul h1
    · exact address_mul h1 (address_mul h1 (by simpa [addressBound] using h2)
        (by simpa only [addressBound, Int.natAbs_natCast] using hmR))
        (address_slot 4 0 R (by omega) (by omega))
    · exact address_power 0 3 h2 (address_slot 0 0 R (by omega) (by omega))
  have hf : (factorCode m).addressBound ≤ R := by
    apply address_mul h1 (address_slot 0 0 R (by omega) (by omega))
    apply address_mul h1
    · exact address_mul h1 (by simpa [addressBound] using h2)
        (by simpa only [addressBound, Int.natAbs_natCast] using hmR)
    · exact address_power 0 3 h2 (address_slot 1 0 R (by omega) (by omega))
  have ho : (outputCode m n).addressBound ≤ R := by
    apply address_table
    intro c hc
    obtain ⟨ji, rfl⟩ := List.mem_ofFn.mp hc
    split_ifs
    · exact address_mul h1 (address_slot 1 0 R (by omega) (by omega))
        (address_slot 5 _ R (by omega) (ji.divNat.isLt.le.trans hn1R))
    · apply address_mul h1 (address_slot 0 0 R (by omega) (by omega))
      apply address_slot 4 _ R (by omega)
      have hp := pairAddress n m ji.divNat.val (ji.modNat.val - 1)
        (by have := ji.divNat.isLt; omega) (by have := ji.modNat.isLt; omega)
      simpa only [R, addressLimit, Nat.add_comm n m] using hp
  simp only [atomCode, addressBound, max_le_iff]
  exact ⟨hu, hc, ht, hg, ha, hk, hh, hn, hf, ho⟩

private theorem birdCell_address (n : ℕ) (i j : Fin n) :
    (birdCell n i j).addressBound ≤ 4 * (n + 1) ^ 2 := by
  let R := 4 * (n + 1) ^ 2
  have hR : 2 ≤ R := by dsimp [R]; ring_nf; omega
  have hcopy (a b : Fin n) : (copy (n * a.val + b.val)).addressBound ≤ R := by
    have h := Nat.mul_le_mul_left n a.isLt.le
    simp only [copy, addressBound, List.foldr_cons, List.foldr_nil, Nat.max_zero]
    dsimp [R]
    nlinarith [b.isLt]
  have hF (a b : Fin n) : (copy (n * n + n * a.val + b.val)).addressBound ≤ R := by
    have h := Nat.mul_le_mul_left n a.isLt.le
    simp only [copy, addressBound, List.foldr_cons, List.foldr_nil, Nat.max_zero]
    dsimp [R]
    nlinarith [b.isLt]
  apply address_add (by omega)
  · apply address_mul (by omega) _ (hcopy i j)
    apply address_neg
    apply address_sum _ _ (by omega)
    intro c hc
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
    split_ifs
    · exact hF k k
    · exact Nat.zero_le _
  · apply address_sum _ _ (by omega)
    intro c hc
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
    split_ifs
    · exact address_mul (by omega) (hF i k) (hcopy k j)
    · exact Nat.zero_le _

private theorem determinant_address (n : ℕ) :
    (determinant n).addressBound ≤ 4 * (n + 1) ^ 2 := by
  let R := 4 * (n + 1) ^ 2
  have hR : 2 ≤ R := by dsimp [R]; ring_nf; omega
  have hn : n * n ≤ R := by dsimp [R]; ring_nf; omega
  have hstage : (birdStage n).addressBound ≤ R := by
    apply max_le (address_range _ |>.trans hn)
    apply address_table
    intro c hc
    obtain ⟨ij, rfl⟩ := List.mem_ofFn.mp hc
    exact birdCell_address n _ _
  cases n with
  | zero => simp [determinant, addressBound]
  | succ k =>
    have hout : (birdStage (k + 1)).outputs ≤ R := by
      rw [birdStage_outputs]
      dsimp [R]
      nlinarith
    have hi := address_iterate _ k R hstage hout
    simp only [determinant, addressBound, max_le_iff]
    refine ⟨⟨address_range _ |>.trans hn, address_range _ |>.trans hn⟩, hi, ?_⟩
    exact address_mul (by omega) (by simp [addressBound]; omega)
      (by simpa [copy, addressBound] using hn)

private theorem squareAddress (m n i j : ℕ) (hi : i ≤ m + 1) (hj : j ≤ m + 1) :
    m * i + j ≤ addressLimit m n := by
  have hmul := Nat.mul_le_mul_left m hi
  dsimp [addressLimit]
  ring_nf at hmul ⊢
  omega

private theorem nonbasicMax_address (e : Fin m → Fin n) (f : Fin n → Code) (R : ℕ)
    (hR : 1 ≤ R) (hf : ∀ j, (f j).addressBound ≤ R) : (nonbasicMax e f).addressBound ≤ R := by
  apply address_maxList _ _ hR
  intro c hc
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
  split_ifs
  · exact Nat.zero_le _
  · exact address_max hR (hf j) (Nat.zero_le _)

private theorem initial_addresses (e : Fin m → Fin n) :
    ∀ c ∈ [basisCode e, determinant m, gCode m], c.addressBound ≤ addressLimit m n := by
  let R := addressLimit m n
  have h10 : 10 ≤ R := (addressFacts m n).1
  have h1 : 1 ≤ R := by omega
  have hd : (determinant m).addressBound ≤ R := (determinant_address m).trans (by
    apply Nat.mul_le_mul_left 4
    apply Nat.pow_le_pow_left
    omega)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · apply address_table
    intro c hc
    obtain ⟨ij, rfl⟩ := List.mem_ofFn.mp hc
    exact address_slot 0 _ R (by omega) (pairAddress m n ij.divNat.val (e ij.modNat).val
      (by have := ij.divNat.isLt; omega) (by have := (e ij.modNat).isLt; omega))
  · exact hd
  · apply address_table
    intro c hc
    obtain ⟨ij, rfl⟩ := List.mem_ofFn.mp hc
    apply address_mul h1 (address_sign (address_slot 0 0 R (by omega) (by omega)))
    apply max_le _ hd
    apply address_table
    intro c hc
    obtain ⟨ab, rfl⟩ := List.mem_ofFn.mp hc
    split_ifs
    · simpa [addressBound] using h1
    · exact Nat.zero_le _
    · exact address_slot 1 _ R (by omega) (squareAddress m n ab.divNat.val ab.modNat.val
        (by have := ab.divNat.isLt; omega) (by have := ab.modNat.isLt; omega))

private theorem cache_addresses (e : Fin m → Fin n) (matrix : Code)
    (hmatrix : matrix.addressBound ≤ addressLimit m n) :
    ∀ c ∈ preparationCaches e matrix, c.addressBound ≤ addressLimit m n := by
  let R := addressLimit m n
  have hf := addressFacts m n
  have h10 : 10 ≤ R := hf.1
  have h1 : 1 ≤ R := by omega
  have hmR : m ≤ R := by have := hf.2.1; omega
  have hnR : n ≤ R := by have := hf.2.1; omega
  have hleaf (block : ℕ) (hb : block ≤ 7) (i : Fin m) (j : Fin n) :
      (slot block (n * i.val + j.val)).addressBound ≤ R :=
    address_slot _ _ R (by omega) (pairAddress m n i.val j.val
      (by have := i.isLt; omega) (by have := j.isLt; omega))
  have hsquare (block : ℕ) (hb : block ≤ 7) (i k : Fin m) :
      (slot block (m * i.val + k.val)).addressBound ≤ R :=
    address_slot _ _ R (by omega) (squareAddress m n i.val k.val
      (by have := i.isLt; omega) (by have := k.isLt; omega))
  have hs (block : ℕ) (hb : block ≤ 7) (i : Fin m) : (slot block i.val).addressBound ≤ R :=
    address_slot _ _ R (by omega) (i.isLt.le.trans hmR)
  have hcost (i : Fin n) : (slot 7 i.val).addressBound ≤ R :=
    address_slot _ _ R (by omega) (i.isLt.le.trans hnR)
  have ha : (canonicalA m n).addressBound ≤ R := by
    apply address_table
    intro c hc
    obtain ⟨ij, rfl⟩ := List.mem_ofFn.mp hc
    apply address_sum _ _ h1
    intro c hc
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
    exact address_mul h1 (hsquare 0 (by decide) ij.divNat k) (hleaf 3 (by decide) k ij.modNat)
  have hb : (canonicalB m).addressBound ≤ R := by
    apply address_table
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    apply address_mul h1 (by simpa [addressBound] using (by omega : 2 ≤ R))
    apply address_sum _ _ h1
    intro c hc
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
    exact address_mul h1 (hsquare 1 (by decide) i k) (hs 5 (by decide) k)
  have hc : (canonicalC e).addressBound ≤ R := by
    apply address_table
    intro c hc
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    apply address_sub h1
    · exact address_mul h1 (address_abs (address_slot 3 0 R (by omega) (by omega))) (hcost j)
    · apply address_sum _ _ h1
      intro c hc
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
      exact address_mul h1 (hleaf 1 (by decide) i j) (hcost (e i))
  have hcoef : (shieldCoefficient e).addressBound ≤ R := by
    apply address_add h1 (address_abs (address_slot 4 0 R (by omega) (by omega)))
    apply nonbasicMax_address e _ R h1
    intro j
    apply address_sum _ _ h1
    intro c hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    exact address_mul h1 (hs 1 (by decide) i)
      (address_max h1 (hleaf 2 (by decide) i j) (Nat.zero_le _))
  have hw : (shieldWeight e).addressBound ≤ R := by
    apply address_add h1 (address_slot 0 0 R (by omega) (by omega))
    apply nonbasicMax_address e _ R h1
    intro j
    apply address_sum _ _ h1
    intro c hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    exact address_mul h1 (hleaf 3 (by decide) i j) (hleaf 3 (by decide) i j)
  have hread (block count : ℕ) (hb : block ≤ R) (hn : count ≤ R) :
      (readAt block (List.range count)).addressBound ≤ R :=
    max_le hb ((address_range _).trans hn)
  intro c hc'
  rcases List.mem_append.mp hc' with hc' | hc'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · simp only [finishCaches, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl
    · exact max_le (hread 4 m (by omega) hmR) (by simpa [addressBound] using h1)
    · exact max_le (hread 4 n (by omega) hnR) (Nat.zero_le _)
    · exact hread 0 _ (by omega) (by have := hf.2.1; omega)
    · exact hread 2 _ (by omega) (by have := hf.2.1; omega)
    · apply hread 4 _ (by omega)
      dsimp [R, addressLimit]
      ring_nf
      omega

private theorem shieldMatrix_address (e : Fin m → Fin n) :
    (shieldMatrix e).addressBound ≤ addressLimit m n := by
  have hf := addressFacts m n
  apply address_table
  intro c hc
  obtain ⟨ij, rfl⟩ := List.mem_ofFn.mp hc
  unfold shieldEntry
  split_ifs
  all_goals first
    | exact Nat.zero_le _
    | exact address_abs (address_slot 6 0 _ (by omega) (by omega))
    | exact address_neg (address_slot 1 0 _ (by omega) (by omega))
    | exact address_slot 4 _ _ (by omega) (pairAddress m n ij.divNat.val ij.modNat.val
        (by have := ij.divNat.isLt; omega) (by have := ij.modNat.isLt; omega))

private theorem weightedMatrix_address (e : Fin m → Fin n) (σ : Equiv.Perm (Fin n)) :
    (weightedMatrix e σ).addressBound ≤ addressLimit m n := by
  let R := addressLimit m n
  have hf := addressFacts m n
  have h10 : 10 ≤ R := hf.1
  have h1 : 1 ≤ R := by omega
  have hw : (slot 0 0).addressBound ≤ R := address_slot 0 0 R (by omega) (by omega)
  have hr (j : Fin n) : (literal (((σ j).val + 1 : ℕ) : ℤ)).addressBound ≤ R := by
    simp only [addressBound, Int.natAbs_natCast]
    have := (σ j).isLt
    have := hf.2.1
    omega
  have hn : (literal ((n + 1 : ℕ) : ℤ)).addressBound ≤ R := by
    simp only [addressBound, Int.natAbs_natCast]
    have := hf.2.1
    omega
  apply address_table
  intro c hc
  obtain ⟨ij, rfl⟩ := List.mem_ofFn.mp hc
  unfold weightedEntry
  split_ifs
  all_goals first
    | exact Nat.zero_le _
    | exact address_mul h1 (hr _) hw
    | exact address_neg (address_mul h1 (hr _) hw)
    | exact address_mul h1 hn hw
    | exact address_slot 4 _ R (by omega) (pairAddress m n ij.divNat.val ij.modNat.val
        (by have := ij.divNat.isLt; omega) (by have := ij.modNat.isLt; omega))

private theorem preparation_address (e : Fin m → Fin n) (matrix : Code)
    (hm : matrix.addressBound ≤ addressLimit m n) :
    (cacheChain [basisCode e, determinant m, gCode m]
      (cacheChain (preparationCaches e matrix) (atomCode (m + 1) (n + 1)))).addressBound ≤
      addressLimit (m + 1) (n + 1) := by
  have hR : addressLimit m n ≤ addressLimit (m + 1) (n + 1) := by
    dsimp [addressLimit]
    gcongr <;> omega
  apply address_chain _ _ _ (fun c hc ↦ (initial_addresses e c hc).trans hR)
  exact address_chain _ _ _ (fun c hc ↦ (cache_addresses e matrix hm c hc).trans hR)
    (atomCode_address (m + 1) (n + 1))

theorem shieldCode_address (e : Fin m → Fin n) :
    (shieldCode e).addressBound ≤ addressLimit (m + 1) (n + 1) := by
  rw [shieldCode_prefix]
  exact preparation_address e _ (shieldMatrix_address e)

theorem weightedCode_address (e : Fin m → Fin n) (σ : Equiv.Perm (Fin n)) :
    (weightedCode e σ).addressBound ≤ addressLimit (m + 1) (n + 1) := by
  rw [weightedCode_prefix]
  exact preparation_address e _ (weightedMatrix_address e σ)

end WolfeSimplex.Execution
