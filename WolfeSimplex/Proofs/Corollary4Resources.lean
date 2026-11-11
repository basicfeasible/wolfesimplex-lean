import WolfeSimplex.Proofs.RationalPreprocessBounds
import WolfeSimplex.Construction.Cap
import WolfeSimplex.Construction.SizeBounds
import WolfeSimplex.Execution.Budget
import WolfeSimplex.Construction.RationalEncoding

set_option maxRecDepth 8000
set_option exponentiation.threshold 1024

/-! Uniform bit bounds for the two reduction pipelines. Parameters are the
dense rational input dimensions and a bound on numerator/denominator width.
The target construction does not inspect the source run or its length. -/
namespace WolfeSimplex.PaperCorollary4.Resources
open Finset Construction
variable {m n : ℕ} (R : RatLP m n)

def integerWidth (L : ℕ) : ℕ := (L + 1) * (n + 2)
def capWidth (L : ℕ) : ℕ := (m + n + 2 + integerWidth (n := n) L) * (m + 2)

theorem integer_max (L : ℕ) (hR : R.EntriesBounded (2 ^ L)) :
    R.integerize.maxEntry ≤ 2 ^ integerWidth (n := n) L := by
  have hmono : R.EntriesBounded (2 ^ (L + 1)) := by
    have hp : 2 ^ L ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact ⟨fun i j ↦ ⟨((hR.1 i j).1.trans hp), ((hR.1 i j).2.trans hp)⟩,
      fun i ↦ ⟨((hR.2.1 i).1.trans hp), ((hR.2.1 i).2.trans hp)⟩,
      fun j ↦ ⟨((hR.2.2 j).1.trans hp), ((hR.2.2 j).2.trans hp)⟩⟩
  obtain ⟨ha, hb, hc⟩ := RatLP.Executed.integerize_entries_le R _
    (Nat.one_le_pow _ _ (by decide)) hmono
  have htwo : 2 ≤ (2 ^ (L + 1)) ^ (n + 2) := by
    rw [← pow_mul]
    have hp : 0 < (L + 1) * (n + 2) := Nat.mul_pos (by omega) (by omega)
    exact (by norm_num : 2 ≤ 2 ^ 1).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have h : R.integerize.maxEntry ≤ (2 ^ (L + 1)) ^ (n + 2) := by
    unfold IntLP.maxEntry
    exact max_le htwo (max_le (max_le (Finset.sup_le fun ij _ ↦ ha ij.1 ij.2)
      (Finset.sup_le fun i _ ↦ hb i)) (Finset.sup_le fun j _ ↦ hc j))
  simpa only [IntLP.maxEntry, ← pow_mul, integerWidth] using h

theorem cap_base (L : ℕ) (hR : R.EntriesBounded (2 ^ L)) :
    Cap.base R.integerize ≤ 2 ^ (m + n + 2 + integerWidth (n := n) L) := by
  have hd : m + n + 2 ≤ 2 ^ (m + n + 2) := Nat.lt_two_pow_self.le
  calc Cap.base R.integerize ≤ 2 ^ (m + n + 2) * 2 ^ integerWidth (n := n) L :=
        Nat.mul_le_mul hd (integer_max R L hR)
       _ = _ := by rw [← pow_add]

theorem capped_max (L : ℕ) (hR : R.EntriesBounded (2 ^ L)) :
    R.integerize.cap.maxEntry ≤ 2 ^ capWidth (m := m) (n := n) L := by
  calc _ ≤ Cap.base R.integerize ^ (m + 2) := Cap.cap_maxEntry _
       _ ≤ (2 ^ (m + n + 2 + integerWidth (n := n) L)) ^ (m + 2) :=
         Nat.pow_le_pow_left (cap_base R L hR) _
       _ = _ := by rw [← pow_mul]; rfl

private theorem bits_of_le_pow {a K : ℕ} (h : a ≤ 2 ^ K) : Nat.size a ≤ K + 1 := by
  apply Nat.size_le.mpr
  exact h.trans_lt (by rw [pow_succ]; have := pow_pos (by decide : 0 < 2) K; omega)

theorem capped_inputSize (L : ℕ) (hR : R.EntriesBounded (2 ^ L)) :
    inputSize R.integerize.cap ≤ 1000 * (m + n + L + 3) ^ 5 := by
  let d := m + n + L + 3
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hs : (m + 1) + (n + 1) + 1 ≤ d := by dsimp [d]; omega
  have hI : integerWidth (n := n) L ≤ d ^ 2 := by
    dsimp [integerWidth]
    simpa only [pow_two] using Nat.mul_le_mul (by dsimp [d]; omega : L + 1 ≤ d)
      (by dsimp [d]; omega : n + 2 ≤ d)
  have hC : capWidth (m := m) (n := n) L ≤ 2 * d ^ 3 := by
    have hh : m + n + 2 ≤ d := by dsimp [d]; omega
    have hm : m + 2 ≤ d := by dsimp [d]; omega
    calc _ ≤ (d + d ^ 2) * d := by dsimp [capWidth]; gcongr
         _ ≤ 2 * d ^ 3 := by nlinarith [sq_nonneg (d - 1 : ℤ)]
  have hw : Nat.size R.integerize.cap.maxEntry ≤ 2 * d ^ 3 + 1 :=
    (bits_of_le_pow (capped_max R L hR)).trans (by omega)
  have h1 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
  calc inputSize R.integerize.cap ≤ 10 * d ^ 2 * (1 + (2 * d ^ 3 + 1)) :=
        (inputSize_le_width _).trans (by gcongr)
       _ ≤ 1000 * d ^ 5 := by nlinarith [Nat.mul_le_mul_left (d ^ 2) h1]

/-- Arithmetic, dense traversal and index charges for the concrete cap program. -/
def capBitWork : ℕ := (Cap.run R.integerize).work *
  (1 + Nat.size (Cap.run R.integerize).peak + (m + n + 2)) ^ 2

theorem cap_bitWork (hm : 1 ≤ m) (L : ℕ) (hR : R.EntriesBounded (2 ^ L)) :
    capBitWork R ≤ 10000 * (m + n + L + 3) ^ 8 := by
  let d := m + n + L + 3
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hshape : m + n + 2 ≤ d := by dsimp [d]; omega
  have hI : integerWidth (n := n) L ≤ d ^ 2 := by
    dsimp [integerWidth]
    simpa only [pow_two] using Nat.mul_le_mul (by dsimp [d]; omega : L + 1 ≤ d)
      (by dsimp [d]; omega : n + 2 ≤ d)
  have hC : capWidth (m := m) (n := n) L ≤ 2 * d ^ 3 := by
    have hm : m + 2 ≤ d := by dsimp [d]; omega
    calc _ ≤ (d + d ^ 2) * d := by dsimp [capWidth]; gcongr
         _ ≤ 2 * d ^ 3 := by nlinarith
  have hp : (Cap.run R.integerize).peak ≤ 2 ^ capWidth (m := m) (n := n) L := by
    exact (Cap.run_peak _ hm).trans ((Nat.pow_le_pow_left (cap_base R L hR) _).trans
      (by rw [← pow_mul]; rfl))
  have hw : Nat.size (Cap.run R.integerize).peak ≤ 2 * d ^ 3 + 1 :=
    (bits_of_le_pow hp).trans (by omega)
  have hb : 1 + Nat.size (Cap.run R.integerize).peak + (m + n + 2) ≤ 5 * d ^ 3 := by
    have h13 := Nat.one_le_pow 3 d hd
    have hd3 : d ≤ d ^ 3 := by simpa using Nat.pow_le_pow_right hd (by decide : 1 ≤ 3)
    omega
  calc capBitWork R ≤ (200 * d ^ 2) * (5 * d ^ 3) ^ 2 := by
        unfold capBitWork
        exact Nat.mul_le_mul ((Cap.run_work _).trans (by gcongr)) (Nat.pow_le_pow_left hb _)
       _ ≤ 10000 * d ^ 8 := by nlinarith [show (200 * d ^ 2) * (5 * d ^ 3) ^ 2 = 5000 * d ^ 8 by ring]

/-- Both full pipelines have a uniform polynomial bit budget. The much larger
exponent for the shortest-atom query reduction comes from canonicalization,
shielding and the existing division-free determinant program. -/
theorem pipelines (hm : 1 ≤ m) (e : Fin (m + 1) → Fin (n + 1))
    (L : ℕ) (hR : R.EntriesBounded (2 ^ L)) :
    RatLP.Executed.bitWork R + capBitWork R +
        (Execution.atomCode (m + 1) (n + 1)).bitWork (Execution.lpInput R.integerize.cap) ≤
      10 ^ 100 * (m + n + L + 3) ^ 200 ∧
    RatLP.Executed.bitWork R + capBitWork R +
        (Execution.shieldCode e).bitWork (Execution.lpInput R.integerize.cap) ≤
      10 ^ 200 * (m + n + L + 3) ^ 200 := by
  let d := m + n + L + 3
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hs := capped_inputSize R L hR
  change inputSize R.integerize.cap ≤ 1000 * d ^ 5 at hs
  have hpre : RatLP.Executed.bitWork R ≤ 1000 * d ^ 8 :=
    (RatLP.Executed.bitWork_bound R L hR).trans (by dsimp [d]; gcongr <;> omega)
  have hcap : capBitWork R ≤ 10000 * d ^ 8 := cap_bitWork R hm L hR
  have hsize : 1 + inputSize R.integerize.cap ≤ 1001 * d ^ 5 := by
    have := Nat.one_le_pow 5 d hd; omega
  have ha := Execution.atom_bitWork R.integerize.cap (by omega)
  have hq := (Execution.shield_certificate R.integerize.cap e (by omega)).2.2.2
  have h8 : d ^ 8 ≤ d ^ 200 := Nat.pow_le_pow_right hd (by decide)
  have h60 : d ^ 60 ≤ d ^ 200 := Nat.pow_le_pow_right hd (by decide)
  have h190 : d ^ 190 ≤ d ^ 200 := Nat.pow_le_pow_right hd (by decide)
  have ha' : (Execution.atomCode (m + 1) (n + 1)).bitWork
      (Execution.lpInput R.integerize.cap) ≤ (10 ^ 30 * 1001 ^ 12) * d ^ 60 := by
    calc _ ≤ 10 ^ 30 * (1001 * d ^ 5) ^ 12 := ha.trans (by gcongr)
         _ = _ := by rw [mul_pow, ← pow_mul]; simp only [Nat.reduceMul, Nat.mul_assoc]
  have hq' : (Execution.shieldCode e).bitWork (Execution.lpInput R.integerize.cap) ≤
      (10 ^ 50 * 1001 ^ 38) * d ^ 190 := by
    calc _ ≤ 10 ^ 50 * (1001 * d ^ 5) ^ 38 := hq.trans (by gcongr)
         _ = _ := by rw [mul_pow, ← pow_mul]; simp only [Nat.reduceMul, Nat.mul_assoc]
  constructor
  · have hc : 1000 + 10000 + 10 ^ 30 * 1001 ^ 12 ≤ (10 ^ 100 : ℕ) := by norm_num
    calc _ ≤ 1000 * d ^ 200 + 10000 * d ^ 200 + (10 ^ 30 * 1001 ^ 12) * d ^ 200 :=
          Nat.add_le_add (Nat.add_le_add (hpre.trans (Nat.mul_le_mul_left _ h8))
            (hcap.trans (Nat.mul_le_mul_left _ h8))) (ha'.trans (Nat.mul_le_mul_left _ h60))
         _ = (1000 + 10000 + 10 ^ 30 * 1001 ^ 12) * d ^ 200 := by rw [Nat.add_mul, Nat.add_mul]
         _ ≤ _ := Nat.mul_le_mul_right _ hc
  · have hc : 1000 + 10000 + 10 ^ 50 * 1001 ^ 38 ≤ (10 ^ 200 : ℕ) := by norm_num
    calc _ ≤ 1000 * d ^ 200 + 10000 * d ^ 200 + (10 ^ 50 * 1001 ^ 38) * d ^ 200 :=
          Nat.add_le_add (Nat.add_le_add (hpre.trans (Nat.mul_le_mul_left _ h8))
            (hcap.trans (Nat.mul_le_mul_left _ h8))) (hq'.trans (Nat.mul_le_mul_left _ h190))
         _ = (1000 + 10000 + 10 ^ 50 * 1001 ^ 38) * d ^ 200 := by rw [Nat.add_mul, Nat.add_mul]
         _ ≤ _ := Nat.mul_le_mul_right _ hc

def countCost : ℕ := RatLP.Executed.bitWork R + capBitWork R +
  (Execution.atomCode (m + 1) (n + 1)).bitWork (Execution.lpInput R.integerize.cap)

def queryCost (e : Fin (m + 1) → Fin (n + 1)) : ℕ :=
  RatLP.Executed.bitWork R + capBitWork R +
    (Execution.shieldCode e).bitWork (Execution.lpInput R.integerize.cap)

theorem binary_pipelines (hm : 1 ≤ m) (e : Fin (m + 1) → Fin (n + 1)) :
    countCost R ≤ 10 ^ 300 * (1 + R.inputSize) ^ 200 ∧
      queryCost R e ≤ 10 ^ 400 * (1 + R.inputSize) ^ 200 := by
  have h := pipelines R hm e R.inputSize R.entries_bounded
  have hd := R.dimensions_le
  have hp : m + n + R.inputSize + 3 ≤ 3 * (1 + R.inputSize) := by omega
  constructor
  · calc countCost R ≤ 10 ^ 100 * (m + n + R.inputSize + 3) ^ 200 := h.1
         _ ≤ 10 ^ 100 * (3 * (1 + R.inputSize)) ^ 200 :=
           Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp _)
         _ = (10 ^ 100 * 3 ^ 200) * (1 + R.inputSize) ^ 200 := by rw [mul_pow, Nat.mul_assoc]
         _ ≤ _ := Nat.mul_le_mul_right _ (by
           calc 10 ^ 100 * 3 ^ 200 ≤ 10 ^ 100 * 10 ^ 200 :=
                 Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide : 3 ≤ 10) _)
                _ = 10 ^ 300 := by rw [← pow_add])
  · calc queryCost R e ≤ 10 ^ 200 * (m + n + R.inputSize + 3) ^ 200 := h.2
         _ ≤ 10 ^ 200 * (3 * (1 + R.inputSize)) ^ 200 :=
           Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp _)
         _ = (10 ^ 200 * 3 ^ 200) * (1 + R.inputSize) ^ 200 := by rw [mul_pow, Nat.mul_assoc]
         _ ≤ _ := Nat.mul_le_mul_right _ (by
           calc 10 ^ 200 * 3 ^ 200 ≤ 10 ^ 200 * 10 ^ 200 :=
                 Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide : 3 ≤ 10) _)
                _ = 10 ^ 400 := by rw [← pow_add])
/-- The programs whose costs are bounded above compute the actual reduction
data. These equalities link the native rational/cap stages to the first-order
integer atom and shortest-start programs. -/
theorem programs_correct (e : Fin (m + 1) → Fin (n + 1)) :
    (RatLP.Executed.run R).value = R.integerize ∧
    (Cap.run (RatLP.Executed.run R).value).value = R.integerize.cap ∧
    (Execution.atomCode (m + 1) (n + 1)).eval
      (Execution.lpInput (Cap.run (RatLP.Executed.run R).value).value) =
        Execution.pack (Execution.integerAtoms R.integerize.cap) ∧
    (Execution.shieldCode e).eval
      (Execution.lpInput (Cap.run (RatLP.Executed.run R).value).value) =
        Execution.pack (Execution.integerAtoms (R.integerize.cap.shieldLP e)) := by
  rw [RatLP.Executed.run_correct, Cap.run_correct]
  exact ⟨rfl, rfl,
    by simpa only [List.append_nil] using Execution.atomCode_correct R.integerize.cap [],
    by simpa only [List.append_nil] using Execution.shieldCode_correct R.integerize.cap e []⟩

end WolfeSimplex.PaperCorollary4.Resources
