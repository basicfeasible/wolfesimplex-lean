import WolfeSimplex.Proofs.RationalPreprocess
import WolfeSimplex.Efficiency.Polynomial

/-! Resource bounds for the actual denominator-clearing program. -/

namespace WolfeSimplex.RatLP
open Finset Construction Construction.Computation
variable {m n : ℕ} (R : RatLP m n)

def EntriesBounded (B : ℕ) : Prop :=
  (∀ i j, (R.A i j).num.natAbs ≤ B ∧ (R.A i j).den ≤ B) ∧
    (∀ i, (R.b i).num.natAbs ≤ B ∧ (R.b i).den ≤ B) ∧
    (∀ j, (R.c j).num.natAbs ≤ B ∧ (R.c j).den ≤ B)

namespace Executed

theorem product_bound (xs : List ℤ) (B : ℕ) (hB : 1 ≤ B)
    (hx : ∀ a ∈ xs, a.natAbs ≤ B) :
    (product xs).peak ≤ B ^ xs.length ∧ (product xs).value.natAbs ≤ B ^ xs.length := by
  induction xs with
  | nil => simp [product]
  | cons a xs ih =>
    have ha := hx a (by simp)
    have ht := ih (fun b hb ↦ hx b (by simp [hb]))
    have hv : xs.prod.natAbs ≤ B ^ xs.length := by simpa only [product_value] using ht.2
    have hp : B ^ xs.length ≤ B ^ (xs.length + 1) :=
      Nat.pow_le_pow_right hB (by omega)
    have hbase : B ≤ B ^ (xs.length + 1) := by
      simpa only [pow_one] using Nat.pow_le_pow_right hB
        (by omega : 1 ≤ xs.length + 1)
    have hm : a.natAbs * xs.prod.natAbs ≤ B ^ (xs.length + 1) := by
      calc _ ≤ B * B ^ xs.length := Nat.mul_le_mul ha hv
           _ = _ := by rw [pow_succ]; exact Nat.mul_comm _ _
    constructor
    · change max (product xs).peak
        (max a.natAbs (max (product xs).value.natAbs
          (a * (product xs).value).natAbs)) ≤ B ^ (xs.length + 1)
      simp only [product_value, Int.natAbs_mul, max_le_iff]
      exact ⟨ht.1.trans hp, ha.trans hbase, hv.trans hp, hm⟩
    · simpa only [product_value, List.prod_cons, List.length_cons, Int.natAbs_mul] using hm

theorem cell_bound (xs : List ℤ) (a : ℤ) (B : ℕ) (hB : 1 ≤ B)
    (hx : ∀ b ∈ xs, b.natAbs ≤ B) (ha : a.natAbs ≤ B) :
    (do let p ← product xs; mul a p).peak ≤ B ^ (xs.length + 1) := by
  have ht := product_bound xs B hB hx
  have hp : B ^ xs.length ≤ B ^ (xs.length + 1) :=
    Nat.pow_le_pow_right hB (by omega)
  have hbase : B ≤ B ^ (xs.length + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hB
      (by omega : 1 ≤ xs.length + 1)
  have hm : a.natAbs * (product xs).value.natAbs ≤ B ^ (xs.length + 1) := by
    calc _ ≤ B * B ^ xs.length := Nat.mul_le_mul ha ht.2
         _ = _ := by rw [pow_succ]; exact Nat.mul_comm _ _
  change max (product xs).peak
    (max a.natAbs (max (product xs).value.natAbs
      (a * (product xs).value).natAbs)) ≤ _
  simp only [Int.natAbs_mul, max_le_iff]
  exact ⟨ht.1.trans hp, ha.trans hbase, ht.2.trans hp, hm⟩

private theorem aWeights_bound (B : ℕ) (hB : 1 ≤ B) (hR : R.EntriesBounded B)
    (i : Fin m) (j : Fin n) : ∀ a ∈ aWeights R i j, a.natAbs ≤ B := by
  intro a ha
  simp only [aWeights, List.mem_append, List.mem_ofFn, List.mem_singleton] at ha
  rcases ha with ⟨k, rfl⟩ | rfl
  · by_cases hk : k = j
    · simpa only [ite_eq_left hk, Int.ofNat_eq_natCast, Int.natAbs_natCast] using hB
    · simpa only [ite_eq_right hk, Int.ofNat_eq_natCast, Int.natAbs_natCast] using (hR.1 i k).2
  · simpa using (hR.2.1 i).2

private theorem bWeights_bound (B : ℕ) (hR : R.EntriesBounded B) (i : Fin m) :
    ∀ a ∈ bWeights R i, a.natAbs ≤ B := by
  intro a ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
  simpa using (hR.1 i j).2

private theorem cWeights_bound (B : ℕ) (hB : 1 ≤ B) (hR : R.EntriesBounded B)
    (j : Fin n) : ∀ a ∈ cWeights R j, a.natAbs ≤ B := by
  intro a ha
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
  by_cases hk : k = j
  · simpa only [ite_eq_left hk, Int.ofNat_eq_natCast, Int.natAbs_natCast] using hB
  · simpa only [ite_eq_right hk, Int.ofNat_eq_natCast, Int.natAbs_natCast] using (hR.2.2 k).2

private theorem pure_peak {α : Type} (a : α) : (pure a : Construction.Computation α).peak = 0 := rfl

theorem run_peak (B : ℕ) (hB : 1 ≤ B) (hR : R.EntriesBounded B) :
    (run R).peak ≤ B ^ (n + 2) := by
  simp only [run, peak_bind, pure_peak, max_le_iff, table_peak]
  refine ⟨?_, ?_, ?_, Nat.zero_le _⟩
  · apply Finset.sup_le
    intro i _
    apply Finset.sup_le
    intro j _
    simpa only [aWeights, List.length_append, List.length_ofFn, List.length_singleton,
      Nat.add_assoc, Nat.reduceAdd, peak_bind] using cell_bound (aWeights R i j) (R.A i j).num B hB
        (aWeights_bound R B hB hR i j) (hR.1 i j).1
  · apply Finset.sup_le
    intro i _
    have h := cell_bound (bWeights R i) (R.b i).num B hB
      (bWeights_bound R B hR i) (hR.2.1 i).1
    simp only [bWeights, List.length_ofFn] at h
    exact h.trans (Nat.pow_le_pow_right hB (by omega))
  · apply Finset.sup_le
    intro j _
    have h := cell_bound (cWeights R j) (R.c j).num B hB
      (cWeights_bound R B hB hR j) (hR.2.2 j).1
    simp only [cWeights, List.length_ofFn] at h
    exact h.trans (Nat.pow_le_pow_right hB (by omega))

theorem run_operations : (run R).operations =
    m * n * (n + 2) + m * (n + 1) + n * (n + 1) := by
  simp [run, aWeights, bWeights, cWeights, mul, binary] <;> ring

theorem run_bookkeeping : (run R).bookkeeping =
    (1 + 4 * m + m * (1 + 4 * n + n * (2 * n + 5))) +
    (1 + 4 * m + m * (2 * n + 3)) +
    (1 + 4 * n + n * (2 * n + 3)) + 4 := by
  simp [run, aWeights, bWeights, cWeights, mul] <;> ring

theorem run_work : (run R).work ≤ 100 * (m + n + 1) ^ 3 := by
  rw [work, run_operations, run_bookkeeping]
  let d := m + n + 1
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hm : m ≤ d := by dsimp [d]; omega
  have hn : n ≤ d := by dsimp [d]; omega
  calc
    _ ≤ d * d * (d + 2) + d * (d + 1) + d * (d + 1) +
        ((1 + 4 * d + d * (1 + 4 * d + d * (2 * d + 5))) +
        (1 + 4 * d + d * (2 * d + 3)) + (1 + 4 * d + d * (2 * d + 3)) + 4) := by
      gcongr
    _ ≤ 100 * d ^ 3 := by
      have h1 := Nat.pow_le_pow_right hd (by decide : 1 ≤ 3)
      have h2 := Nat.pow_le_pow_right hd (by decide : 2 ≤ 3)
      have h0 := Nat.one_le_pow 3 d hd
      simp only [pow_one] at h1
      ring_nf at *
      omega

theorem run_word (L : ℕ) (hR : R.EntriesBounded (2 ^ L)) :
    Nat.size (run R).peak ≤ L * (n + 2) + 1 := by
  have hp := run_peak R (2 ^ L) (Nat.one_le_pow L 2 (by decide)) hR
  rw [← pow_mul] at hp
  apply Nat.size_le.mpr
  apply lt_of_le_of_lt hp
  rw [pow_succ]
  have hpos : 0 < 2 ^ (L * (n + 2)) := pow_pos (by decide) _
  omega

/-- Charge arithmetic and bookkeeping at a conservative word cost, including
the indices of the finite input/output tables. -/
def bitWork : ℕ :=
  (run R).work * (1 + Nat.size (run R).peak + (m + n + 1)) ^ 2

theorem bitWork_bound (L : ℕ) (hR : R.EntriesBounded (2 ^ L)) :
    bitWork R ≤ 1000 * (m + n + L + 2) ^ 8 := by
  let d := m + n + L + 2
  have hd : 2 ≤ d := by dsimp [d]; omega
  have hshape : m + n + 1 ≤ d := by dsimp [d]; omega
  have hn : n + 2 ≤ d := by dsimp [d]; omega
  have hL : L ≤ d := by dsimp [d]; omega
  have hw : (run R).work ≤ 100 * d ^ 3 :=
    (run_work R).trans (by gcongr)
  have hword := run_word R L hR
  have hprod : L * (n + 2) ≤ d ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hL hn
  have hbits : 1 + Nat.size (run R).peak + (m + n + 1) ≤ 3 * d ^ 2 := by
    nlinarith
  have hp : d ^ 7 ≤ d ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  calc
    bitWork R ≤ (100 * d ^ 3) * (3 * d ^ 2) ^ 2 := by
      unfold bitWork
      gcongr
    _ = 900 * d ^ 7 := by ring
    _ ≤ 900 * d ^ 8 := Nat.mul_le_mul_left _ hp
    _ ≤ 1000 * d ^ 8 := Nat.mul_le_mul_right _ (by decide)

theorem cell_value_bound (xs : List ℤ) (a : ℤ) (B : ℕ) (hB : 1 ≤ B)
    (hx : ∀ b ∈ xs, b.natAbs ≤ B) (ha : a.natAbs ≤ B) :
    (do let p ← product xs; mul a p).value.natAbs ≤ B ^ (xs.length + 1) := by
  have hv := (product_bound xs B hB hx).2
  change (a * (product xs).value).natAbs ≤ _
  rw [Int.natAbs_mul]
  calc _ ≤ B * B ^ xs.length := Nat.mul_le_mul ha hv
       _ = _ := by rw [pow_succ]; exact Nat.mul_comm _ _

theorem integerize_entries_le (B : ℕ) (hB : 1 ≤ B) (hR : R.EntriesBounded B) :
    (∀ i j, (R.integerize.A i j).natAbs ≤ B ^ (n + 2)) ∧
    (∀ i, (R.integerize.b i).natAbs ≤ B ^ (n + 2)) ∧
    (∀ j, (R.integerize.c j).natAbs ≤ B ^ (n + 2)) := by
  refine ⟨fun i j ↦ ?_, fun i ↦ ?_, fun j ↦ ?_⟩
  · have h := cell_value_bound (aWeights R i j) (R.A i j).num B hB
      (aWeights_bound R B hB hR i j) (hR.1 i j).1
    have he := congrArg (fun P : IntLP m n ↦ P.A i j) (run_correct R)
    simp only [run, value_bind, value_pure, table_value] at he
    simp only [value_bind] at h
    rw [he] at h
    simpa only [aWeights, List.length_append, List.length_ofFn, List.length_singleton,
      Nat.add_assoc, Nat.reduceAdd] using h
  · have h := cell_value_bound (bWeights R i) (R.b i).num B hB
      (bWeights_bound R B hR i) (hR.2.1 i).1
    have he := congrArg (fun P : IntLP m n ↦ P.b i) (run_correct R)
    simp only [run, value_bind, value_pure, table_value] at he
    simp only [value_bind] at h
    rw [he] at h
    simp only [bWeights, List.length_ofFn] at h
    exact h.trans (Nat.pow_le_pow_right hB (by omega))
  · have h := cell_value_bound (cWeights R j) (R.c j).num B hB
      (cWeights_bound R B hB hR j) (hR.2.2 j).1
    have he := congrArg (fun P : IntLP m n ↦ P.c j) (run_correct R)
    simp only [run, value_bind, value_pure, table_value] at he
    simp only [value_bind] at h
    rw [he] at h
    simp only [cWeights, List.length_ofFn] at h
    exact h.trans (Nat.pow_le_pow_right hB (by omega))

end Executed
end WolfeSimplex.RatLP
