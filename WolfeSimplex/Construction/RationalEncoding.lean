import WolfeSimplex.Proofs.RationalPreprocessBounds
import WolfeSimplex.Construction.Encoding

/-! A concrete dense binary encoding, with unary dimension headers (linear in
the number of dense input cells). Rational numbers store numerator and positive
denominator separately. -/
namespace WolfeSimplex.RatLP
open Construction
variable {m n : ℕ} (R : RatLP m n)

def data : List ℚ :=
  (List.ofFn fun i : Fin m ↦ List.ofFn fun j : Fin n ↦ R.A i j).flatten ++
    List.ofFn R.b ++ List.ofFn R.c

def encodeRat (q : ℚ) : List Bool := encodeInt q.num ++ encodeNat q.den

def encoding : List Bool :=
  List.replicate m false ++ [true] ++ List.replicate n false ++ [true] ++
    R.data.flatMap encodeRat

def inputSize : ℕ := R.encoding.length

theorem inputSize_eq : inputSize R = m + n + 2 + (R.data.map fun q ↦ (encodeRat q).length).sum := by
  simp [inputSize, encoding, List.length_flatMap, List.map_map, Function.comp_def]
  omega

theorem dimensions_le : m + n + 2 ≤ inputSize R := by rw [inputSize_eq]; omega

private theorem member_width {xs : List ℚ} {q : ℚ} (hq : q ∈ xs) :
    Nat.size q.num.natAbs ≤ (xs.map fun q ↦ (encodeRat q).length).sum ∧
    Nat.size q.den ≤ (xs.map fun q ↦ (encodeRat q).length).sum := by
  have hle : (encodeRat q).length ≤ (xs.map fun q ↦ (encodeRat q).length).sum := by
    induction xs with
    | nil => simp at hq
    | cons a xs ih =>
      simp only [List.mem_cons] at hq
      simp only [List.map_cons, List.sum_cons]
      rcases hq with rfl | hq
      · omega
      · have := ih hq; omega
  have hn : Nat.size q.num.natAbs ≤ (encodeRat q).length := by
    simp only [encodeRat, List.length_append, encodeInt_length, encodeNat_length]; omega
  have hd : Nat.size q.den ≤ (encodeRat q).length := by
    simp only [encodeRat, List.length_append, encodeInt_length, encodeNat_length]; omega
  exact ⟨hn.trans hle, hd.trans hle⟩

theorem entries_bounded : R.EntriesBounded (2 ^ inputSize R) := by
  have hmem (q : ℚ) (hq : q ∈ R.data) :
      q.num.natAbs ≤ 2 ^ inputSize R ∧ q.den ≤ 2 ^ inputSize R := by
    have hw := member_width hq
    have hn : Nat.size q.num.natAbs ≤ inputSize R := by rw [inputSize_eq]; omega
    have hd : Nat.size q.den ≤ inputSize R := by rw [inputSize_eq]; omega
    exact ⟨(Nat.lt_size_self q.num.natAbs).le.trans (Nat.pow_le_pow_right (by decide) hn),
      (Nat.lt_size_self q.den).le.trans (Nat.pow_le_pow_right (by decide) hd)⟩
  refine ⟨fun i j ↦ hmem _ ?_, fun i ↦ hmem _ ?_, fun j ↦ hmem _ ?_⟩
  · apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, List.mem_ofFn.mpr ⟨j, rfl⟩⟩
  · apply List.mem_append_left
    exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨j, rfl⟩)

theorem inputSize_le (L : ℕ) (hR : R.EntriesBounded (2 ^ L)) :
    inputSize R ≤ 100 * (m + n + L + 3) ^ 3 := by
  have hc (q : ℚ) (hq : q ∈ R.data) : (encodeRat q).length ≤ 4 * L + 7 := by
    have hb : q.num.natAbs ≤ 2 ^ L ∧ q.den ≤ 2 ^ L := by
      rcases List.mem_append.mp hq with hq | hq
      · rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨row, hr, hq⟩ := List.mem_flatten.mp hq
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
          obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
          exact hR.1 i j
        · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq; exact hR.2.1 i
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq; exact hR.2.2 j
    have hpow : 2 ^ L < 2 ^ (L + 1) := by
      rw [pow_succ]; have := pow_pos (by decide : 0 < 2) L; omega
    have hn := Nat.size_le.mpr (hb.1.trans_lt hpow)
    have hd := Nat.size_le.mpr (hb.2.trans_lt hpow)
    simp only [encodeRat, List.length_append, encodeInt_length, encodeNat_length]
    omega
  have hs : (R.data.map fun q ↦ (encodeRat q).length).sum ≤ R.data.length * (4 * L + 7) := by
    have aux : ∀ xs : List ℚ, (∀ q ∈ xs, (encodeRat q).length ≤ 4 * L + 7) →
        (xs.map fun q ↦ (encodeRat q).length).sum ≤ xs.length * (4 * L + 7) := by
      intro xs hx
      induction xs with
      | nil => simp
      | cons a xs ih =>
        have ha := hx a (by simp)
        have ht := ih (fun q hq ↦ hx q (by simp [hq]))
        simp only [List.map_cons, List.sum_cons, List.length_cons]; nlinarith
    exact aux R.data hc
  have hl : R.data.length = m * n + m + n := by
    simp [data, List.length_flatten, Function.comp_def]; omega
  rw [hl] at hs
  let d := m + n + L + 3
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hcount : m * n + m + n ≤ d ^ 2 := by dsimp [d]; nlinarith
  have hword : 4 * L + 7 ≤ 7 * d := by dsimp [d]; omega
  have hdim : m + n + 2 ≤ d := by dsimp [d]; omega
  have hd3 : d ≤ d ^ 3 := by simpa using Nat.pow_le_pow_right hd (by decide : 1 ≤ 3)
  rw [inputSize_eq]
  calc _ ≤ d + d ^ 2 * (7 * d) := Nat.add_le_add hdim (hs.trans (Nat.mul_le_mul hcount hword))
       _ ≤ 100 * d ^ 3 := by nlinarith [show d ^ 2 * (7 * d) = 7 * d ^ 3 by ring]

end WolfeSimplex.RatLP
