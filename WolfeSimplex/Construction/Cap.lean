import WolfeSimplex.Construction.Work
import WolfeSimplex.Defs.Cap

/-! Concrete cap construction and its resource bounds. -/
namespace WolfeSimplex.Construction.Cap
open Finset Construction.Computation
variable {m n : ℕ} (P : IntLP m n)

private theorem mul_value (a b : ℤ) : (mul a b).value = a * b := rfl
private theorem add_value (a b : ℤ) : (add a b).value = a + b := rfl
private theorem mul_operations (a b : ℤ) : (mul a b).operations = 1 := rfl
private theorem add_operations (a b : ℤ) : (add a b).operations = 1 := rfl
private theorem uScan_operations : (uScan P).operations = 2 * (m * n + m) + 1 := by
  simp [uScan, maxAbs, constraintData, List.length_flatten, Function.comp_def]

def run : Construction.Computation (IntLP (m + 1) (n + 1)) := do
  let u ← uScan P
  let mu ← mul m u
  let pw ← power mu m
  let bound ← mul m pw
  let rhs ← add bound 1
  let a ← table fun i : Fin (m + 1) ↦ table fun j : Fin (n + 1) ↦ add 0 (P.cap.A i j)
  let b ← table fun i : Fin (m + 1) ↦ add 0 (Fin.snoc (α := fun _ ↦ ℤ) P.b rhs i)
  let costs ← table fun j : Fin (n + 1) ↦ add 0 (Fin.snoc (α := fun _ ↦ ℤ) P.c 0 j)
  pure ⟨fun i j ↦ a[i][j], fun i ↦ b[i], fun j ↦ costs[j]⟩

theorem run_correct : (run P).value = P.cap := by
  have hp : ((m : ℤ) * (P.U : ℤ)) ^ m = (((m * P.U) ^ m : ℕ) : ℤ) := by simp
  have hr : (m : ℤ) * ((m : ℤ) * (P.U : ℤ)) ^ m + 1 = (P.capBound : ℤ) + 1 := by
    rw [hp]; simp only [IntLP.capBound, Nat.cast_mul]
  simp only [run, value_bind, uScan_value, mul, binary, power_value, add,
    zero_add, table_value, hr, value_pure]
  rfl

theorem run_work : (run P).work ≤ 200 * (m + n + 2) ^ 2 := by
  simp only [run, work, operations_bind, bookkeeping_bind, uScan_bookkeeping,
    uScan_operations, power_operations, power_bookkeeping,
    mul_operations, add_operations, table_operations, table_bookkeeping,
    operations_pure, bookkeeping_pure, add, mul, binary_bookkeeping]
  simp only [binary, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  nlinarith

def base : ℕ := (m + n + 2) * P.maxEntry

theorem base_facts : 2 ≤ base P ∧ P.maxEntry ≤ base P ∧ m ≤ base P := by
  have hw := P.two_le_maxEntry
  dsimp [base]
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem cap_entries :
    (∀ i j, (P.cap.A i j).natAbs ≤ base P ^ (m + 2)) ∧
    (∀ i, (P.cap.b i).natAbs ≤ base P ^ (m + 2)) ∧
    (∀ j, (P.cap.c j).natAbs ≤ base P ^ (m + 2)) := by
  let B := base P
  have hb : 2 ≤ B := (base_facts P).1
  have hw : P.maxEntry ≤ B := (base_facts P).2.1
  have hm : m ≤ B := (base_facts P).2.2
  have hsmall : B ≤ B ^ (m + 2) := Nat.le_self_pow (by omega) B
  have hmu : m * P.U ≤ B := by
    dsimp [B, base]
    exact Nat.mul_le_mul (by omega) P.U_le_maxEntry
  have hcap : P.capBound + 1 ≤ B ^ (m + 2) := by
    have ht : P.capBound ≤ B ^ (m + 1) := by
      calc P.capBound = m * (m * P.U) ^ m := rfl
           _ ≤ B * B ^ m := Nat.mul_le_mul hm (Nat.pow_le_pow_left hmu _)
           _ = B ^ (m + 1) := by rw [pow_succ]; exact Nat.mul_comm _ _
    have hp := Nat.one_le_pow (m + 1) B (by omega)
    rw [pow_succ]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    induction i using Fin.lastCases with
    | last => simpa [IntLP.cap] using (by omega : 1 ≤ B ^ (m + 2))
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [IntLP.cap]
      | cast j => simpa [IntLP.cap] using
          (P.natAbs_A_le i j).trans (P.U_le_maxEntry.trans (hw.trans hsmall))
  · intro i
    induction i using Fin.lastCases with
    | last =>
      rw [show P.cap.b (Fin.last m) = ((P.capBound + 1 : ℕ) : ℤ) by simp [IntLP.cap],
        Int.natAbs_natCast]
      exact hcap
    | cast i => simpa [IntLP.cap] using
        (P.natAbs_b_le i).trans (P.U_le_maxEntry.trans (hw.trans hsmall))
  · intro j
    induction j using Fin.lastCases with
    | last => simp [IntLP.cap]
    | cast j =>
      have hc : (P.c j).natAbs ≤ P.maxEntry := by
        unfold IntLP.maxEntry
        exact (P.natAbs_c_le j).trans ((le_max_right _ _).trans (le_max_right _ _))
      simpa [IntLP.cap] using hc.trans (hw.trans hsmall)

theorem cap_maxEntry : P.cap.maxEntry ≤ base P ^ (m + 2) := by
  obtain ⟨hA, hb, hc⟩ := cap_entries P
  have h2 : 2 ≤ base P ^ (m + 2) :=
    (base_facts P).1.trans (Nat.le_self_pow (by omega) _)
  unfold IntLP.maxEntry
  exact max_le h2 (max_le (max_le (Finset.sup_le fun ij _ ↦ hA ij.1 ij.2)
    (Finset.sup_le fun i _ ↦ hb i)) (Finset.sup_le fun j _ ↦ hc j))

theorem run_peak (hm : 1 ≤ m) : (run P).peak ≤ base P ^ (m + 2) := by
  let B := base P
  let R := B ^ (m + 2)
  have hb : 2 ≤ B := (base_facts P).1
  have hsmall : B ≤ R := Nat.le_self_pow (by omega) B
  have hw : P.maxEntry ≤ R := (base_facts P).2.1.trans hsmall
  have hmB : m ≤ B := (base_facts P).2.2
  have hmR : m ≤ R := hmB.trans hsmall
  have hu : P.U ≤ R := P.U_le_maxEntry.trans hw
  have hmu : m * P.U ≤ B := by
    dsimp [B, base]; exact Nat.mul_le_mul (by omega) P.U_le_maxEntry
  have hp : (m * P.U) ^ m ≤ R :=
    (Nat.pow_le_pow_left hmu _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hbound : P.capBound ≤ R := by
    have ht := (cap_entries P).2.1 (Fin.last m)
    have he : (P.cap.b (Fin.last m)).natAbs = P.capBound + 1 := by
      rw [show P.cap.b (Fin.last m) = ((P.capBound + 1 : ℕ) : ℤ) by simp [IntLP.cap],
        Int.natAbs_natCast]
    rw [he] at ht; exact (by omega : P.capBound ≤ P.capBound + 1).trans ht
  have hrhs : P.capBound + 1 ≤ R := by
    have ht := (cap_entries P).2.1 (Fin.last m)
    rw [show P.cap.b (Fin.last m) = ((P.capBound + 1 : ℕ) : ℤ) by simp [IntLP.cap],
      Int.natAbs_natCast] at ht
    exact ht
  have hpow := power_peak_le (a := (m : ℤ) * (P.U : ℤ)) (by
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    simpa only [one_mul] using Nat.mul_le_mul hm P.one_le_U) m
  have he : ((m : ℤ) * (P.U : ℤ)) ^ m = (((m * P.U) ^ m : ℕ) : ℤ) := by simp
  have hr : (m : ℤ) * ((m : ℤ) * (P.U : ℤ)) ^ m + 1 = ((P.capBound + 1 : ℕ) : ℤ) := by
    rw [he]; simp only [IntLP.capBound, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  simp only [Int.natAbs_mul, Int.natAbs_natCast, ← Nat.mul_pow] at hpow
  have hpowR := hpow.trans hp
  have ha : ∀ i j, (add 0 (P.cap.A i j)).peak ≤ R := by
    intro i j; simpa [add, binary] using (cap_entries P).1 i j
  have hbr : ∀ i, (add 0 (P.cap.b i)).peak ≤ R := by
    intro i; simpa [add, binary] using (cap_entries P).2.1 i
  have hc : ∀ j, (add 0 (P.cap.c j)).peak ≤ R := by
    intro j; simpa [add, binary] using (cap_entries P).2.2 j
  simp only [run, peak_bind, uScan_value, mul_value, add_value, power_value, he, hr,
    peak_pure, table_peak, max_le_iff, Finset.sup_le_iff]
  refine ⟨?_, ?_, hpowR, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · have hs : (uScan P).peak = P.U := by
      simp only [uScan, materialize_peak, maxAbs_peak]
      exact uScan_value P
    rw [hs]; exact hu
  · simpa only [mul, binary, Int.natAbs_mul, Int.natAbs_natCast, max_le_iff] using
      And.intro hmR (And.intro hu (hmu.trans hsmall))
  · simpa only [mul, binary, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast,
      ← Nat.mul_pow, IntLP.capBound, max_le_iff] using
      And.intro hmR (And.intro hp hbound)
  · simp only [add, binary]
    rw [show (m : ℤ) * (((m * P.U) ^ m : ℕ) : ℤ) = (P.capBound : ℤ) by
      simp [IntLP.capBound]]
    rw [show (P.capBound : ℤ) + 1 = ((P.capBound + 1 : ℕ) : ℤ) by simp]
    simpa only [Int.natAbs_natCast, Int.natAbs_one, max_le_iff] using
      And.intro hbound (And.intro (by omega : 1 ≤ R) hrhs)
  · exact fun i _ j _ ↦ ha i j
  · intro i _; exact hbr i
  · intro j _; exact hc j

end WolfeSimplex.Construction.Cap
