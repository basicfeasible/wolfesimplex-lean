import WolfeSimplex.Execution.Addresses
import WolfeSimplex.Construction.Encoding

namespace WolfeSimplex.Execution
open Code
variable {m n : ℕ}

/-- Signed data, literal addresses and work/control counters are all included. -/
def Code.wordWidth (c : Code) (env : Env) : ℕ :=
  1 + Nat.size (c.run env).peak + Nat.size c.addressBound + Nat.size (c.run env).work

def Code.bitWork (c : Code) (env : Env) : ℕ := (c.run env).work * (c.wordWidth env) ^ 2

private theorem size_mul (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  apply Nat.size_le.mpr
  calc a * b ≤ a * 2 ^ Nat.size b := Nat.mul_le_mul_left _ (Nat.lt_size_self b).le
       _ < 2 ^ Nat.size a * 2 ^ Nat.size b :=
          Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity)
       _ = _ := by rw [pow_add]

/-- Full word width for the main atom constructor, with no basis or
admissibility assumption beyond a positive row count. -/
theorem atom_wordWidth (P : IntLP m n) (hm : 1 ≤ m) :
    (atomCode m n).wordWidth (lpInput P) ≤ 2001637 * Construction.sizeParameter P ^ 4 := by
  let L := Construction.sizeParameter P
  have hL : 1 ≤ L := by dsimp [L, Construction.sizeParameter]; omega
  have hM : m + 1 ≤ L := by dsimp [L, Construction.sizeParameter]; omega
  have hd : m + n + 1 ≤ L := by dsimp [L, Construction.sizeParameter]; omega
  have hbase : Nat.size ((m + 1) * P.maxEntry) ≤ L := Construction.base_size_le P
  have hL3 : 1 ≤ L ^ 3 := Nat.one_le_pow _ _ hL
  have hpeak : ((atomCode m n).run (lpInput P)).peak ≤ P.N ^ 2 * P.K := by
    simpa only [List.append_nil] using atomCode_peak P hm []
  have hnum : 1 + Nat.size ((atomCode m n).run (lpInput P)).peak ≤ 37 * L ^ 3 := by
    have hn := hpeak.trans (P.N_sq_mul_K_le hm)
    have hb := IntLP.magnitude_bits_le (z := (((atomCode m n).run (lpInput P)).peak : ℤ))
      (b := (m + 1) * P.maxEntry) (e := 36 * (m + 1) ^ 2) (by positivity)
      (by simpa only [Int.natAbs_natCast] using hn)
    calc _ ≤ 1 + 36 * (m + 1) ^ 2 * Nat.size ((m + 1) * P.maxEntry) := Nat.add_le_add_left hb 1
         _ ≤ 1 + 36 * L ^ 2 * L := by gcongr
         _ ≤ _ := by nlinarith only [hL3]
  have hmeta : Nat.size (atomCode m n).addressBound ≤ 1600 * L ^ 2 := by
    apply (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    apply (atomCode_address m n).trans
    change 4 * (m + n + 20) ^ 2 ≤ _
    calc _ ≤ 4 * (20 * L) ^ 2 := by gcongr; omega
         _ = _ := by ring
  have hwork : Nat.size ((atomCode m n).run (lpInput P)).work ≤ 2000000 * L ^ 4 := by
    apply (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    exact (atomCode_work P).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd 4))
  have h24 : L ^ 2 ≤ L ^ 4 := Nat.pow_le_pow_right hL (by decide)
  have h34 : L ^ 3 ≤ L ^ 4 := Nat.pow_le_pow_right hL (by decide)
  change 1 + Nat.size ((atomCode m n).run (lpInput P)).peak +
    Nat.size (atomCode m n).addressBound + Nat.size ((atomCode m n).run (lpInput P)).work ≤ 2001637 * L ^ 4
  nlinarith only [hnum, hmeta, hwork, h24, h34]

theorem atom_bitWork (P : IntLP m n) (hm : 1 ≤ m) :
    (atomCode m n).bitWork (lpInput P) ≤ 10 ^ 30 * (1 + Construction.inputSize P) ^ 12 := by
  let L := Construction.sizeParameter P
  have hd : m + n + 1 ≤ L := by dsimp [L, Construction.sizeParameter]; omega
  have hw := atom_wordWidth P hm
  have hL : L ≤ 3 * (1 + Construction.inputSize P) := by
    have h := Construction.sizeParameter_le P
    dsimp [L]
    omega
  calc (atomCode m n).bitWork (lpInput P) ≤
          (2000000 * L ^ 4) * (2001637 * L ^ 4) ^ 2 :=
          Nat.mul_le_mul ((atomCode_work P).trans
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd 4))) (Nat.pow_le_pow_left hw 2)
       _ = (2000000 * 2001637 ^ 2) * L ^ 12 := by ring
       _ ≤ (2000000 * 2001637 ^ 2) * (3 * (1 + Construction.inputSize P)) ^ 12 := by gcongr
       _ ≤ _ := by
         rw [mul_pow, ← mul_assoc]
         exact Nat.mul_le_mul_right _ (by norm_num)

/-- Main operational construction certificate: exact values, dimension-only
work, full word width and polynomial bit work in the binary input length. -/
theorem atom_certificate (P : IntLP m n) (hm : 1 ≤ m) :
    (atomCode m n).eval (lpInput P) = pack (integerAtoms P) ∧
    (∀ j k, (integerAtoms P j k : ℝ) = P.atom j k) ∧
    ((atomCode m n).run (lpInput P)).work ≤ 2000000 * (m + n + 1) ^ 4 ∧
    (atomCode m n).wordWidth (lpInput P) ≤ 2001637 * Construction.sizeParameter P ^ 4 ∧
    (atomCode m n).bitWork (lpInput P) ≤ 10 ^ 30 * (1 + Construction.inputSize P) ^ 12 :=
  ⟨by simpa only [List.append_nil] using atomCode_correct P [], integerAtoms_correct P, atomCode_work P,
    atom_wordWidth P hm, atom_bitWork P hm⟩

private theorem preparation_base_bits (P : IntLP m n) :
    Nat.size (preparationBase P) ≤ 3 * (Construction.sizeParameter P + 1) := by
  have hm : Nat.size (m + n + 2) ≤ m + n + 2 := Nat.size_le.mpr Nat.lt_two_pow_self
  have h := (size_mul (2 * (m + n + 2)) P.maxEntry).trans
    (Nat.add_le_add_right ((size_mul 2 (m + n + 2)).trans (Nat.add_le_add_left hm _)) _)
  rw [show Nat.size 2 = 2 from rfl] at h
  change Nat.size (preparationBase P) ≤ _ at h
  dsimp [Construction.sizeParameter]
  omega

/-- A complete width bound for either shortest-start preparation program. -/
theorem preparation_wordWidth (P : IntLP m n) (c : Code)
    (hw : (c.run (lpInput P)).work ≤ 1100000000 * (m + n + 2) ^ 12)
    (hp : (c.run (lpInput P)).peak ≤ preparationBase P ^ preparationExponent m)
    (ha : c.addressBound ≤ addressLimit (m + 1) (n + 1)) :
    c.wordWidth (lpInput P) ≤ 2000000000 * (Construction.sizeParameter P + 1) ^ 13 := by
  let L := Construction.sizeParameter P + 1
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hd : m + n + 2 ≤ L := by dsimp [L, Construction.sizeParameter]; omega
  have hm : m + 2 ≤ L := by omega
  have hL3 : L ^ 3 ≤ L ^ 12 := Nat.pow_le_pow_right hL (by decide)
  have he : preparationExponent m ≤ (5 ^ 11 + 72) * L ^ 12 := by
    have hfirst : (4 * m + 5) ^ 11 * (m + 2) ≤ 5 ^ 11 * L ^ 12 := by
      calc _ ≤ (5 * L) ^ 11 * L := by gcongr; omega
           _ = _ := by rw [mul_pow]; ring
    have hsecond : (2 * m + 4) * 36 * (m + 2) ^ 2 ≤ 72 * L ^ 12 := by
      calc _ ≤ (2 * L) * 36 * L ^ 2 := by gcongr; omega
           _ = 72 * L ^ 3 := by ring
           _ ≤ _ := Nat.mul_le_mul_left _ hL3
    dsimp [preparationExponent]
    nlinarith only [hfirst, hsecond]
  have hnum : 1 + Nat.size (c.run (lpInput P)).peak ≤ 150000000 * L ^ 13 := by
    have hwidth := preparation_width P c hp
    have hbase := preparation_base_bits P
    have hL13 : 1 ≤ L ^ 13 := Nat.one_le_pow _ _ hL
    calc _ ≤ 1 + preparationExponent m * Nat.size (preparationBase P) := hwidth
         _ ≤ 1 + ((5 ^ 11 + 72) * L ^ 12) * (3 * L) := by gcongr
         _ ≤ _ := by norm_num only [Nat.reducePow, Nat.reduceAdd]; nlinarith only [hL13]
  have hmeta : Nat.size c.addressBound ≤ 1936 * L ^ 2 := by
    apply (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    apply ha.trans
    change 4 * (m + 1 + (n + 1) + 20) ^ 2 ≤ _
    calc _ ≤ 4 * (22 * L) ^ 2 := by gcongr; omega
         _ = _ := by ring
  have hc : Nat.size (c.run (lpInput P)).work ≤ 1100000000 * L ^ 12 := by
    apply (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    exact hw.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd 12))
  have h213 : L ^ 2 ≤ L ^ 13 := Nat.pow_le_pow_right hL (by decide)
  have h1213 : L ^ 12 ≤ L ^ 13 := Nat.pow_le_pow_right hL (by decide)
  change 1 + Nat.size (c.run (lpInput P)).peak + Nat.size c.addressBound +
    Nat.size (c.run (lpInput P)).work ≤ 2000000000 * L ^ 13
  nlinarith only [hnum, hmeta, hc, h213, h1213]

/-- Polynomial bit work in the explicit dense binary input length. -/
theorem preparation_bitWork (P : IntLP m n) (c : Code)
    (hw : (c.run (lpInput P)).work ≤ 1100000000 * (m + n + 2) ^ 12)
    (hp : (c.run (lpInput P)).peak ≤ preparationBase P ^ preparationExponent m)
    (ha : c.addressBound ≤ addressLimit (m + 1) (n + 1)) :
    c.bitWork (lpInput P) ≤ 10 ^ 50 * (1 + Construction.inputSize P) ^ 38 := by
  let L := Construction.sizeParameter P + 1
  have hd : m + n + 2 ≤ L := by dsimp [L, Construction.sizeParameter]; omega
  have hb := preparation_wordWidth P c hw hp ha
  have hL : L ≤ 3 * (1 + Construction.inputSize P) := by
    have h := Construction.sizeParameter_le P
    dsimp [L]
    omega
  calc c.bitWork (lpInput P) ≤ (1100000000 * L ^ 12) * (2000000000 * L ^ 13) ^ 2 := by
          exact Nat.mul_le_mul (hw.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd 12)))
            (Nat.pow_le_pow_left hb 2)
       _ = 4400000000000000000000000000 * L ^ 38 := by ring
       _ ≤ 4400000000000000000000000000 * (3 * (1 + Construction.inputSize P)) ^ 38 := by gcongr
       _ ≤ _ := by
         rw [mul_pow, ← mul_assoc]
         exact Nat.mul_le_mul_right _ (by norm_num)

/-- One entry point for the complete resource claims for Lemma 14. -/
theorem shield_certificate (P : IntLP m n) (e : Fin m → Fin n) (hm : 1 ≤ m) :
    (shieldCode e).eval (lpInput P) = pack (integerAtoms (P.shieldLP e)) ∧
    ((shieldCode e).run (lpInput P)).work ≤ 1100000000 * (m + n + 2) ^ 12 ∧
    (shieldCode e).wordWidth (lpInput P) ≤ 2000000000 * (Construction.sizeParameter P + 1) ^ 13 ∧
    (shieldCode e).bitWork (lpInput P) ≤ 10 ^ 50 * (1 + Construction.inputSize P) ^ 38 := by
  have hw := preparation_work P (shieldCode e) (shieldCode_size e)
  have hp := shieldCode_peak P e hm
  have ha := shieldCode_address e
  exact ⟨by simpa only [List.append_nil] using shieldCode_correct P e [], hw,
    preparation_wordWidth P _ hw hp ha, preparation_bitWork P _ hw hp ha⟩

/-- One entry point for the complete resource claims for Lemma 17. -/
theorem weighted_certificate (P : IntLP m n) (e : Fin m → Fin n)
    (σ : Equiv.Perm (Fin n)) (hm : 1 ≤ m) :
    (weightedCode e σ).eval (lpInput P) = pack (integerAtoms (P.weightedLP e σ)) ∧
    ((weightedCode e σ).run (lpInput P)).work ≤ 1100000000 * (m + n + 2) ^ 12 ∧
    (weightedCode e σ).wordWidth (lpInput P) ≤ 2000000000 * (Construction.sizeParameter P + 1) ^ 13 ∧
    (weightedCode e σ).bitWork (lpInput P) ≤ 10 ^ 50 * (1 + Construction.inputSize P) ^ 38 := by
  have hw := preparation_work P (weightedCode e σ) (weightedCode_size e σ)
  have hp := weightedCode_peak P e σ hm
  have ha := weightedCode_address e σ
  exact ⟨by simpa only [List.append_nil] using weightedCode_correct P e σ [], hw,
    preparation_wordWidth P _ hw hp ha, preparation_bitWork P _ hw hp ha⟩

end WolfeSimplex.Execution
